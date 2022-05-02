import ntac.core
import ntac.katex

/-!
# Tactics for literate programming

Tactics for literate programming. Math expressions will be converted into KaTeX math syntax.
Math expressions can be written between `$` marks, or placed in list when using `parse_pexpr_list`.
Notations for identifiers whose name is conflicting with others may not work between `$` marks
(for example, `=` in proofs for pythagorean numbers, which conflicts with the lemma `eq` in the file).
-/
open ntac
open tactic
open lean.parser

namespace ntac.literate
/--parses lean expressions into KaTeX math syntax.-/
meta def parse_to_katex (s: string) : tactic string := do
e ← lean.parser.run_with_input (lean.parser.pexpr 0 tt) $ s, -- "("++s++")" is safer?
exp ← to_expr e,
expr_to_katex exp

/--parses a list into KaTeX syntax.  String (not parsed) and math expression (parsed by `parse_to_katex`) must be placed alternately in the list. Used in `parse_all`.-/
meta def parse_all_list : list string → tactic string
| [] := fail "empty input"
| (str::[]) := pure str
| (str::math::tail) := do s ← parse_to_katex math, ts ← parse_all_list tail, pure $ str ++ "$" ++ s ++ "$" ++ ts

/--a frontend for `parse_all_list`. -/
meta def parse_all (s: string) : tactic string :=
let l := string.split (='$') s in parse_all_list l

meta def antiquote_aux : list char → string
| []  := "(empty input)"
| [c] := ""
| ('\\'::'n':: xs) := "\n"++antiquote_aux xs
| ('\\'::'t':: xs) := "\t"++antiquote_aux xs
| ('\\'::'\\':: xs) := "\\"++antiquote_aux xs
| ('\\'::'\"':: xs) := "\""++antiquote_aux xs
| (x::xs) := x.to_string ++ antiquote_aux xs

/-- the inverse of `string.quote`. -/
meta def antiquote(s: string) :string :=
match s.to_list with
| [] :=""
| x::xs := antiquote_aux xs
end

/--parses `expr` into KaTeX math. If the expression is a `string` literal (beginning with `"`), use `parse_all` for it. -/
meta def parse_pexpr (e: expr): tactic string := 
match e.to_string.to_list with
| [] := "(empty input)"
| '"'::_ := parse_all $ antiquote e.to_string
| _ := do s ← expr_to_katex e, return $ "$"++s++"$"
end

/--parses list of `pexpr` into string. Notations for conflicting identifiers can be used (refer to the beginning of this file).-/
meta def parse_pexpr_list (l: list pexpr) :tactic string:=
do le ← monad.sequence $ list.map to_expr l,
ls ← monad.sequence $ list.map parse_pexpr le,
string.join ls

end ntac.literate

open ntac.literate
namespace ntac.interactive
meta def solve1 : itactic → ntac unit := ntac.solve1

meta def FOCUS1str (tac: itactic) (s: string) : ntac unit := ntac.FOCUS1str tac s
meta def FOCUS1triv (tac: itactic): ntac unit := ntac.FOCUS1triv tac

/--marks a goal as trivial.-/
meta def TRIV : ntac unit :=tac1to1_inf (tactic.skip) inf.triv


meta def FOLD1str (s:string) : ntac unit := tac1to1_inf (tactic.skip) $ inf.ngoals_string detail_cfg.folded s


open interactive interactive.types
meta def texpr_list_or_texpr := (list_of texpr) <|> list.ret <$> texpr

meta def SOL1_str (tac : itactic) (s: string): ntac unit := 
do 
   FOLD1str s,
   solve1 tac

/--A version of `SOL1_str`. "p" stands for "parse", and Lean parses and type-checks input string.-/
meta def SOL1p_str (tac : itactic) (s: string): ntac unit := 
do e ← parse_all s, -- TODO: use `tactic_state` to interpret expressions in the tactic block
   SOL1_str tac e

/--The list version of `SOL1p_str`; for expressions with identifiers interpreted wrongly in string-/
meta def SOL1p_list (tac : itactic) (s: parse texpr_list_or_texpr): ntac unit := 
do e ← parse_pexpr_list s, -- TODO: use `tactic_state` (similar as above)
   SOL1_str tac e


--incomplete ideas
-- meta def FOLD1 (tac : itactic) : ntac unit:= 
-- do a ← tac,
--    g::gs ← get_goals,
-- meta def FOLD1str
-- meta def FOLDall

end ntac.interactive
