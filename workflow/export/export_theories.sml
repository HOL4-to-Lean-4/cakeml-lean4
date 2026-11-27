(* Typed kernel export of every stored theorem, definition and axiom of the milestone-1 theories,
   plus the constants and type operators each theory declares.
   Adapted from candle-hol4-lean4-study/tools/hol4_query/export_statements.sml.
   Run with `hol run` from run_export.sh. Environment: EXPORT_THYS (file with one theory name per
   line), EXPORT_OUT (output file). No proofs are read: the exporter only looks at the stored
   statement of each theory object.
   Terms are raw kernel terms with every type explicit, so no parser, overload or pretty-printer
   setting affects them. Encoding, per record:
     "tys": interned types; a type is "'a" (type variable) or ["thy$tyop", i1, .., in] (indices into tys)
     terms: ["v",name,ty] ["c","thy$name",ty] ["a",f,x] ["l",name,ty,body]   (ty = index into tys) *)
open HolKernel boolLib;

val thys =
  let val f = TextIO.openIn (valOf (OS.Process.getEnv "EXPORT_THYS"))
      fun go acc = case TextIO.inputLine f of
          NONE => rev acc
        | SOME l => let val s = String.implode (List.filter (fn c => not (Char.isSpace c)) (String.explode l))
                    in go (if s = "" then acc else s :: acc) end
      val r = go [] in TextIO.closeIn f; r end;
val _ = List.app (fn t => load (t ^ "Theory")) thys;
val _ = Globals.linewidth := 120;

val outf = TextIO.openOut (valOf (OS.Process.getEnv "EXPORT_OUT"));
fun out s = TextIO.output (outf, s);
fun q s =
  let fun c #"\"" = "\\\"" | c #"\\" = "\\\\" | c #"\n" = "\\n"
        | c x = if Char.ord x < 32 then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord x)) else str x
  in "\"" ^ String.translate c s ^ "\"" end;

(* per-record interning of types *)
val tab : (string, int) Binarymap.dict ref = ref (Binarymap.mkDict String.compare);
val tys : string list ref = ref [];
val cnt = ref 0;
fun reset () = (tab := Binarymap.mkDict String.compare; tys := []; cnt := 0);
fun intern (s : string) =
  case Binarymap.peek (!tab, s) of
    SOME i => i
  | NONE => let val i = !cnt in tab := Binarymap.insert (!tab, s, i); tys := s :: !tys; cnt := i + 1; i end;
fun ty t =
  if is_vartype t then intern (q (dest_vartype t))
  else let val {Thy, Tyop, Args} = dest_thy_type t
           val is = map ty Args
       in intern ("[" ^ String.concatWith "," (q (Thy ^ "$" ^ Tyop) :: map Int.toString is) ^ "]") end;
fun tm t =
  if is_var t then let val (n, y) = dest_var t in "[\"v\"," ^ q n ^ "," ^ Int.toString (ty y) ^ "]" end
  else if is_const t then let val {Thy, Name, Ty} = dest_thy_const t
       in "[\"c\"," ^ q (Thy ^ "$" ^ Name) ^ "," ^ Int.toString (ty Ty) ^ "]" end
  else if is_comb t then let val (f, x) = dest_comb t in let val a = tm f val b = tm x in "[\"a\"," ^ a ^ "," ^ b ^ "]" end end
  else let val (b, body) = dest_abs t
           val (n, y) = dest_var b
           val yi = ty y
           val bs = tm body
       in "[\"l\"," ^ q n ^ "," ^ Int.toString yi ^ "," ^ bs ^ "]" end;
fun tysjson () = "[" ^ String.concatWith "," (rev (!tys)) ^ "]";

fun kind_of DB.Thm = "theorem" | kind_of DB.Def = "definition" | kind_of DB.Axm = "axiom";
fun line_of (DB.Located {linenum, ...}) = Int.toString linenum | line_of _ = "0";
fun thm_rec thy (((_, name), (th, {private, loc, class})) : DB.data) =
  (reset ();
   let val hs = map tm (hyp th)
       val c = tm (concl th)
       val pp = thm_to_string th
   in out ("{\"thy\":" ^ q thy ^ ",\"name\":" ^ q name ^ ",\"kind\":" ^ q (kind_of class)
           ^ ",\"private\":" ^ Bool.toString private ^ ",\"line\":" ^ line_of loc
           ^ ",\"hyps\":[" ^ String.concatWith "," hs ^ "],\"concl\":" ^ c
           ^ ",\"tys\":" ^ tysjson () ^ ",\"pretty\":" ^ q pp ^ "}\n") end)
  handle e => out ("{\"thy\":" ^ q thy ^ ",\"name\":" ^ q name ^ ",\"kind\":\"error\",\"err\":" ^ q (exnMessage e) ^ "}\n");
fun const_rec thy c =
  (reset ();
   let val {Name, Ty, ...} = dest_thy_const c
       val i = ty Ty
   in out ("{\"thy\":" ^ q thy ^ ",\"name\":" ^ q Name ^ ",\"kind\":\"constant\",\"ty\":" ^ Int.toString i
           ^ ",\"tys\":" ^ tysjson () ^ "}\n") end)
  handle e => out ("{\"thy\":" ^ q thy ^ ",\"kind\":\"error\",\"err\":" ^ q (exnMessage e) ^ "}\n");
fun tyop_rec thy (name, arity) =
  out ("{\"thy\":" ^ q thy ^ ",\"name\":" ^ q name ^ ",\"kind\":\"type\",\"arity\":" ^ Int.toString arity ^ "}\n");
fun one thy =
  (List.app (thm_rec thy) (DB.thy thy);
   List.app (const_rec thy) (Theory.constants thy);
   List.app (tyop_rec thy) (Theory.types thy));
val _ = List.app one thys;
val _ = TextIO.closeOut outf;
