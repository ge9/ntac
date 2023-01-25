import ntac.core
import ntac.katex

/-!
# Tactics for literate programming

Tactics for literate programming. Math expressions will be converted into KaTeX math syntax.
Math expressions can be written between `#` marks, or placed in list when using `parse_pexpr_list`.
Notations for identifiers whose name is conflicting with others may not work between `#` marks
(for example, `=` in proofs for pythagorean numbers, which conflicts with the lemma `eq` in the file).
-/
open ntac
open tactic
open lean.parser

namespace ntac.literate
/--parses lean expressions into KaTeX math syntax.-/
meta def parse_to_katex (s: string) : tactic string := do
back ← read,
e ← lean.parser.run_with_input (lean.parser.pexpr 0 tt) $ s, -- "("++s++")" is safer?
exp ← to_expr e,
str ← safe_run $ expr_to_katex exp,
return str

/--parses a list into KaTeX syntax.  String (not parsed) and math expression (parsed by `parse_to_katex`) must be placed alternately in the list. Used in `parse_all`.-/
meta def parse_all_list : list string → tactic string
| [] := fail "empty input"
| (str::[]) := pure str
| (str::math::tail) := do s ← parse_to_katex math, ts ← parse_all_list tail, pure $ str ++ "$" ++ s ++ "$" ++ ts

/--a frontend for `parse_all_list`. -/
meta def parse_all (s: string) : tactic string :=
let l := string.split (='#') s in parse_all_list l

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

/--parses `expr` into KaTeX math. If the expression is a `string` literal (beginning with `"`), `parse_all` is called. -/
meta def parse_expr (e: expr): tactic string := 
match e.to_string.to_list with
| [] := "(empty input)"
| '"'::_ := parse_all $ antiquote e.to_string
| _ := do s ← expr_to_katex e, return $ "$"++s++"$"
end
meta def parse_pexpr1 (p: pexpr) :tactic string:= safe_run $ to_expr p >>= parse_expr

/--parses list of `pexpr` into string. Notations for conflicting identifiers can be used (refer to the beginning of this file).-/
meta def parse_pexpr_list (l: list pexpr) :tactic string:=
safe_run $ do le ← monad.sequence $ list.map to_expr l,
ls ← monad.sequence $ list.map parse_expr le,
string.join ls

end ntac.literate

open ntac.literate
namespace ntac.interactive
meta def solve1 : itactic → ntac unit := ntac.solve1

open interactive interactive.types
meta def texpr_list_or_texpr := (list_of texpr) <|> list.ret <$> texpr
/--The resulting number of goals can be any value (including 0 (solved)).-/
private meta def NTAC_focus1_aux (tac: itactic): ntac ((Π {n : ℕ}, inf n.succ) → goal_tree) := 
do gs ← tactic_to_ntac get_goals,
   match gs with
   | []      := fail "1toN tactic failed, there isn't any goal left to focus"
   | (g::rs) := 
     (do tactic_to_ntac $ set_goals [g],
        gt ← get_goal_tree,
        type ← target,
        let ng_make := replc_unres g gt,--hgより上の部分を切ってバックアップ
        set_goal_tree $ ⟨0, inf.unres g, vector.nil, type⟩,--hgだけをgoal_treeに
        _ ← tac,
        gs' ← tactic_to_ntac $ get_goals,
        --未解決のgoalの箇所をすべて閉じる（type2の部分は使わないが一応入れておく）
        -- さらにtypeのvectorを返す
        let l := gs'.length,
        let gsvec : (vector expr l) := ⟨gs', rfl⟩,
        types ← vector.sequence $ 
        vector.map (λ g2, do type2 ← tactic_to_ntac $ infer_type g2, replc_gi g2 (λ e, ⟨0, inf.closed, vector.nil, type2⟩), pure type2) gsvec,
        let newgts : vector goal_tree l := vector.map₂ (λ ge te, ⟨0, inf.unres ge, vector.nil, te⟩) gsvec types,
        rg ← get_goal_tree,
        set_goals (gs' ++rs),
        --切ったツリーをwillbeNgoal_strの中に入れて元のゴールのところに入れる。最初が{}の中身のgoal_tree、残りがunresolved goal
        return $ λ ii, ng_make $ goal_tree.mk (l+1) ii (vector.cons rg newgts))
   end


/--can be used on a tactic (block) turning a goal into any number of goals. 
The process is considered to be trivial and not reflected on the output.-/
meta def NTAC_focus1_triv (tac: itactic) : ntac unit := 
do f ← NTAC_focus1_aux tac,
set_goal_tree (f (@inf.willbeNgoal_str none))

/--does parse beforehand-/
private meta def NTAC_focus1_b (tac: itactic) (ts: tactic (string × bool)): ntac unit := 
do e ← ts, f ← NTAC_focus1_aux tac,
set_goal_tree (f (@inf.willbeNgoal_str e))

/--does parse afterwards-/
private meta def NTAC_focus1_a (tac: itactic) (ts: tactic (string × bool)): ntac unit := 
do f ← NTAC_focus1_aux tac, e ← ts,
set_goal_tree (f (@inf.willbeNgoal_str e))

/--the argument string describes how the goal is manipulated.  `is_before` specifies the comment is validated before or after the tactics inside.
`detailed` specifies if the detail is shown.-/
private meta def NTAC_focus1 (tac: itactic) (is_before: bool) (detailed: bool) (ts: tactic string) : ntac unit := 
(if is_before then NTAC_focus1_b else NTAC_focus1_a) tac $ do s ← ts, pure $ (s, detailed)


meta def NTAC_focus1_str (tac: itactic) (s: string)  (is_before: bool) (detailed: bool): ntac unit := 
NTAC_focus1 tac is_before detailed $ parse_all s

meta def NTAC_focus1_list (tac: itactic) (s: parse texpr_list_or_texpr) (is_before: bool) (detailed: bool) : ntac unit := 
NTAC_focus1 tac is_before detailed $ parse_pexpr_list s

meta def NTAC_solve1_auto (tac : itactic) : ntac unit := 
do insert_inf1 inf.fold_auto,
   solve1 tac

/--marks a goal as trivial.-/
meta def TRIV : ntac unit := insert_inf1 $ inf.willbeNgoal_str none

/--for debugging; parse expression into KaTeX -/
meta def trace_expr (s: parse texpr) : ntac unit :=
do 
e ← parse_pexpr1 s, trace e

end ntac.interactive
