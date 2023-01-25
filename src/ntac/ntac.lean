import ntac.goal_tree

--To define custom tactic, referred to https://leanprover-community.github.io/archive/stream/113488-general/topic/no.20lean.20messages.20output.20in.20hacked.20mode.html

/--
Monad `ntac`, defined by adding `goal_tree` (information of proof process) to original `tactic_state`.
Tactics from the namespace `ntac.interactive` can be used (instead of those from `tactic.interactive`) by writing `[ntac]` after `begin`.
-/
-- TODO: use some monad transformer?
@[reducible] meta def ntac := interaction_monad (tactic_state × goal_tree)

open tactic
namespace ntac

meta def tactic_to_ntac {α} (t: tactic α): ntac α :=
λ ts,
let (tac, str) := ts in 
let res := t tac in
match res with 
| (result.success a s)       := (result.success a (s,str)) 
| (result.exception t ref s) := (result.exception t ref (s,str))
end

meta def tactic_to_ntac_literate {α} (t: tactic α): ntac α :=
do e ← tactic_to_ntac t,
return e

--use `tactic` as `ntac`
meta instance {α}: has_coe (tactic α) (ntac α) := ⟨tactic_to_ntac⟩

--construct `goal_tree` with the first goal to run ntac as tactic.
meta def ntac_to_tactic {α} (t: ntac α) : tactic α :=
do g::_ ← get_goals,
type ← infer_type g,
kind ← infer_type type,
let goal_tree2 : goal_tree:= ⟨0, inf.unres g, vector.nil, type⟩ in
λ sa,
let res := t (sa, goal_tree2) in
match res with 
| (result.success a s)       := (result.success a s.1) 
| (result.exception t ref s) := (result.exception t ref s.1)
end

--`executor` is required to run a `begin ... end` block as a tactic (?)
meta instance : interactive.executor ntac :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, ntac_to_tactic }

meta instance : alternative ntac :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _,
  ..interaction_monad.monad }

--definitions required to be treated as tactic
meta def step {α} (c : ntac α) : ntac unit := do gs ← tactic_to_ntac get_goals,c >>return ()

---3.32.1 → 3.49.1で修正
meta def istep {α} (line0 col0 line col ast : ℕ) (t : ntac α) : ntac unit :=
λ s, (@scope_trace _ line col (λ _, step t s)).clamp_pos line0 line col
meta def save_info (p : pos) : ntac unit := tactic_to_ntac $ tactic.save_info p
meta def execute (c : ntac unit) : ntac unit := c

meta def fail {α} {β} [has_to_format β] (msg : β) : ntac α := interaction_monad.fail msg
meta def first {α} : list (ntac α) → ntac α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

--utility functions
--meta def change_goal_tree (f:goal_tree → goal_tree) : ntac unit := 
--λ sa, let (tst, goal_tree) := sa in result.success () (tst, f goal_tree)
meta def set_goal_tree (g: goal_tree) : ntac unit :=
λ sa, let (tst, _) := sa in result.success () (tst, g)
meta def get_goal_tree: ntac goal_tree := 
λ sa, let (tst, goal_tree) := sa in result.success goal_tree (tst, goal_tree)
 
/--replc_unresを今のgoal_treeに適用する。よく使うので関数とする-/
meta def replc_gi (e:expr) (g: expr → goal_tree): ntac unit := λ sa, let (tst, goal_tree) := sa in result.success () (tst, replc_unres e goal_tree g)
meta def mk_unres_goal_tree (g: expr) : ntac goal_tree :=
do type ← infer_type g,
kind ← infer_type type, return $ ⟨0, inf.unres g, vector.nil, type⟩ 

--This definition is apparently the same as tactic.solve1, but still needs to be defined separately, because `ntac α` must be run inside. 
meta def solve1 {α} (tac : ntac α) : ntac α :=
do gs ← get_goals,
   match gs with
   | []      := fail "solve1 tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        a ← tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals rs >> pure a
        | gs := fail "solve1 tactic failed, focused goal has not been solved"
        end
   end

meta def solve {α} (ts : list (ntac α)) : ntac α := first $ list.map solve1 ts

private meta def all_goals'_core (tac : ntac unit) : list expr → list expr → ntac unit
| []        ac := tactic_to_ntac $ set_goals ac
| (g :: gs) ac :=
  mcond ( tactic_to_ntac $ is_assigned g) (all_goals'_core gs ac) $
    do tactic_to_ntac $ set_goals [g],
       tac,
       new_gs ←  tactic_to_ntac $ get_goals,
       all_goals'_core gs (ac ++ new_gs)

/-- Apply the given tactic to all goals. -/
meta def all_goals' (tac : ntac unit) : ntac unit :=
do gs ← tactic_to_ntac $ get_goals,
   all_goals'_core tac gs []

meta def skip : ntac unit :=
result.success ()

meta def try {α}(t : ntac α) : ntac unit := λ s,
match t s with
| (result.exception _ _ _) := result.success () s
| (result.success _ s') := result.success () s'
end

end ntac
