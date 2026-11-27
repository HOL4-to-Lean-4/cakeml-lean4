#!/usr/bin/env python3
"""Append rows to ledger/costs.csv (its existing header) from the result of one model call.

usage:  ledger.py INPUT [INPUT ...] --arm ARM --phase PHASE --workflow WORKFLOW [--run 1] [--round ""] [--tool T]
                        [--start UTC] [--end UTC] [--machine M] [--human-minutes N] [--usd-billed X] [--notes TEXT]
                        [--ledger PATH] [--dry-run]

INPUT is one of
  * the output of `claude -p ... --output-format json` (an object with "type":"result", or the array that
    `--verbose` prints), or the stream (`--output-format stream-json`, JSON lines; several `result` lines of a
    resumed run are summed). Tokens come from `usage`, cost from `total_cost_usd` (usd_api_equivalent), the model
    from `modelUsage` (or the assistant messages of a stream), duration from `duration_ms`.
  * a codex / gateway `*.meta.json` (as written by tools/astra_gateway: requested_model, reported_model, usage
    {input_tokens, cached_input_tokens, output_tokens, reasoning_output_tokens}, seconds, utc). Codex counts cached
    tokens inside input_tokens: the uncached part is written.
Start/end default to --start/--end, else the file's mtime minus the duration. A row is skipped if the ledger already has
the same (arm, phase, workflow, run), so re-running is safe. Columns not known from the input are left empty; usd_billed is empty
unless --usd-billed (subscription calls are not billed per token)."""
import argparse, csv, datetime, io, json, os, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def iso(ts):
    return datetime.datetime.fromtimestamp(ts, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def load_json_any(path):
    t = io.open(path, encoding="utf-8", errors="replace").read().strip()
    try:
        o = json.loads(t)
        return o if isinstance(o, list) else [o]
    except json.JSONDecodeError:
        out = []
        for l in t.split("\n"):
            try:
                out.append(json.loads(l))
            except json.JSONDecodeError:
                pass
        return out


def from_claude(objs, path):
    res = [o for o in objs if isinstance(o, dict) and o.get("type") == "result"]
    if not res:
        return None
    tot = {k: 0 for k in ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")}
    cost, dur, models = 0.0, 0, []
    for r in res:
        u = r.get("usage") or {}
        for k in tot:
            tot[k] += u.get(k, 0) or 0
        cost += r.get("total_cost_usd", 0) or 0
        dur += r.get("duration_ms", 0) or 0
        for m in (r.get("modelUsage") or {}):
            if m not in models:
                models.append(m)
    if not models:
        for o in objs:
            if o.get("type") == "assistant":
                m = (o.get("message") or {}).get("model")
                if m and m != "<synthetic>" and m not in models:
                    models.append(m)
    notes = f"session={res[-1].get('session_id', '')};turns={sum(r.get('num_turns', 0) or 0 for r in res)};subtype={res[-1].get('subtype', '')}"
    if any(r.get("is_error") for r in res):
        notes += ";is_error"
    return dict(tool="claude-cli", model_id="+".join(models), input_tokens=tot["input_tokens"], output_tokens=tot["output_tokens"],
                cache_read_tokens=tot["cache_read_input_tokens"], cache_write_tokens=tot["cache_creation_input_tokens"], reasoning_tokens="",
                usd_api_equivalent=round(cost, 4), seconds=dur / 1000.0, notes=notes)


def from_codex_meta(o):
    if not isinstance(o, dict) or "usage" not in o or not (o.get("requested_model") or o.get("reported_model")):
        return None
    u = o.get("usage") or {}
    inp = u.get("input_tokens", 0) or 0
    cached = u.get("cached_input_tokens", 0) or (u.get("input_tokens_details") or {}).get("cached_tokens", 0) or 0
    out_t = u.get("output_tokens", 0) or 0
    reasoning = u.get("reasoning_output_tokens", 0) or (u.get("output_tokens_details") or {}).get("reasoning_tokens", 0) or 0
    note = f"requested={o.get('requested_model')};reported={o.get('reported_model')}"
    if o.get("rc"):
        note += f";rc={o['rc']}"
    return dict(tool="codex-cli" if "codex" in str(o.get("via", "")) else "gateway", model_id=o.get("reported_model") or o.get("requested_model"),
                input_tokens=inp - cached, output_tokens=out_t, cache_read_tokens=cached, cache_write_tokens=u.get("cache_write_input_tokens", 0) or 0,
                reasoning_tokens=reasoning, usd_api_equivalent="", seconds=float(o.get("seconds", 0) or 0), notes=note, utc=o.get("utc"))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+")
    ap.add_argument("--arm", required=True)
    ap.add_argument("--phase", required=True)
    ap.add_argument("--workflow", required=True)
    ap.add_argument("--run", default="1")
    ap.add_argument("--round", default="")
    ap.add_argument("--tool")
    ap.add_argument("--start")
    ap.add_argument("--end")
    ap.add_argument("--machine", default=os.environ.get("LEDGER_MACHINE", "cloud"))
    ap.add_argument("--human-minutes", default="0")
    ap.add_argument("--usd-billed", default="")
    ap.add_argument("--notes", default="")
    ap.add_argument("--ledger", default=os.path.join(REPO, "ledger", "costs.csv"))
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    rows = list(csv.reader(io.open(a.ledger, encoding="utf-8", newline="")))
    H = rows[0]
    ai, phi, wi, ri = H.index("arm"), H.index("phase"), H.index("workflow"), H.index("run")
    have = {(r[ai], r[phi], r[wi], r[ri]) for r in rows[1:] if len(r) > ri}
    new = []
    for p in a.inputs:
        objs = load_json_any(p)
        d = from_claude(objs, p) or (from_codex_meta(objs[0]) if objs else None)
        if d is None:
            sys.exit(f"{p}: neither a Claude Code result nor a codex/gateway meta.json")
        mt = os.path.getmtime(p)
        end = a.end or d.get("utc") or iso(mt)
        start = a.start or iso(mt - d["seconds"])
        wf = a.workflow if len(a.inputs) == 1 else f"{a.workflow}-{os.path.splitext(os.path.basename(p))[0]}"
        if (a.arm, a.phase, wf, a.run) in have:
            print("skip (already in ledger):", wf, a.run)
            continue
        rec = {"arm": a.arm, "phase": a.phase, "round": a.round, "workflow": wf, "run": a.run, "tool": a.tool or d["tool"], "model_id": d["model_id"],
               "start_utc": start, "end_utc": end, "input_tokens": d["input_tokens"], "output_tokens": d["output_tokens"],
               "cache_read_tokens": d["cache_read_tokens"], "cache_write_tokens": d["cache_write_tokens"], "reasoning_tokens": d["reasoning_tokens"],
               "usd_billed": a.usd_billed, "usd_api_equivalent": d["usd_api_equivalent"], "human_minutes": a.human_minutes, "machine": a.machine,
               "notes": ";".join(x for x in (d["notes"], a.notes) if x)}
        unknown = set(rec) - set(H)
        if unknown:
            sys.exit("ledger header lacks columns: " + ", ".join(sorted(unknown)))
        new.append([rec.get(h, "") for h in H])
        have.add((wf, a.run))
    for r in new:
        print(",".join(str(x) for x in r))
    if new and not a.dry_run:
        with io.open(a.ledger, "a", encoding="utf-8", newline="") as f:
            csv.writer(f, lineterminator="\n").writerows(new)
    print(f"{len(new)} row(s) {'would be ' if a.dry_run else ''}appended to {a.ledger}")


if __name__ == "__main__":
    main()
