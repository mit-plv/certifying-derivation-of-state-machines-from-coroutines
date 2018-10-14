(*i camlp4deps: "grammar/grammar.cma" i*)

open Stdarg
open Ltac_plugin

DECLARE PLUGIN "plugin"

TACTIC EXTEND is_fix
| [ "match_fix" constr(c) ] ->
  [ let env = Global.env () in
    let evd = Evd.from_env env in
    if EConstr.isFix evd c then Tacticals.New.tclIDTAC else Tacticals.New.tclFAIL 0 (Pp.str "not a fixpoint") ]
END
