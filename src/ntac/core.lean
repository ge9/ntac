/-Some utility functions and interactive tactics. Roughly corresponds to `init/meta/tactic.lean`. Some definitions are like copy-paste.-/
import ntac.ntac
import system.io
open tactic

namespace ntac

meta def getgoal1 : ntac expr := 
do g::_ ← get_goals,
return g
meta def getgoalinfo1 : ntac goal_tree := 
do g::_ ← get_goals,
ti ← infer_type g,
return $ ⟨0, inf.unres g, vector.nil, ti⟩

meta def getgoalinfos : ntac (list goal_tree) := 
do goals ← get_goals,
   goal_ti ← monad.sequence $ list.map (λ e, infer_type e) goals,
   let goal_trees := list.map inf.unres goals in
   let goal_trees:list goal_tree := list.zip_with (λ inf0 ti, ⟨0, inf0, vector.nil, ti⟩) goal_trees goal_ti in
  return goal_trees

meta def getgoal1_or_done : ntac (option goal_tree) := 
do gs ← get_goals,
match gs with
| g::_ := do ti ← infer_type g, return (⟨0, inf.unres g, vector.nil, ti⟩:goal_tree)
| _ := return none
end

meta def tac1to1_inf {α} (tac : ntac α) (inf1 : inf 1) : (ntac α) :=
do hg ← getgoal1,
e ← tac,
g ← getgoal1,
type ← target,
kind ← infer_type type,
replc_gi hg $ goal_tree.mk 1 inf1 ⟨[⟨0, inf.unres g, vector.nil, type⟩],dec_trivial⟩, return e
  
/--migrated from `tactic.focus1`-/
meta def focus1 {α} (tac : ntac α) : ntac α :=
do g::gs ← get_goals,
   match gs with
   | [] := tac
   | _  := do
      set_goals [g],
      a ← tac,
      gs' ← get_goals,
      set_goals (gs' ++ gs),
      return a
   end

/--a version of `focus1`; attach string to tactic(s) applied to 1 goal-/
meta def focus1_to_n_inf {α} (tac : ntac α) (s: ∀{n:ℕ}, inf n): ntac α := 
do gs ← tactic_to_ntac get_goals,
   match gs with
   | []      := fail "1toN tactic failed, there isn't any goal left to focus"
   | (g::rs) := 
     (do tactic_to_ntac $ set_goals [g],
        gi_bak ← get_goal_tree,--protect goal_tree from `tac`
        a ← tac,
        gs' ← tactic_to_ntac $ get_goals,
        set_goal_tree gi_bak,
        (let l := gs'.length in
        let gs_vec : vector expr l := ⟨gs', rfl⟩ in do goal_tree_vec ← vector.sequence $ vector.map mk_unres_goal_tree gs_vec,
        replc_gi g $ goal_tree.mk l s goal_tree_vec 
        ),
        set_goals (gs' ++rs),
        return a)
   end

meta def FOCUS1str {α} (tac : ntac α) (s: string): ntac α := 
focus1_to_n_inf tac (@inf.ngoals_string detail_cfg.following s)
meta def FOCUS1triv {α} (tac : ntac α): ntac α := 
focus1_to_n_inf tac @inf.ngoals_triv

namespace interactive
/--this seems necessary to define custom tactic combinators. The name should be exactly `itactic`-/
meta def itactic := ntac unit

@[inline] meta def read2 : ntac tactic_state :=
λ s, let (tac, str) := s in
  result.success tac s

meta def pp {α} [has_to_tactic_format α] (a:α) : ntac format :=
has_to_tactic_format.to_tactic_format a

meta instance : has_to_tactic_format (tactic format) := ⟨id⟩

meta def trace {α} [has_to_tactic_format α] (a : α) : ntac unit :=
do fmt ← pp a,
   return $ _root_.trace_fmt fmt (λ u, ())
meta def trace_goals : ntac unit :=
do gs ← get_goals,
  let gs_str := list.map to_string gs,
  trace $ string.join gs_str
meta def trace_goals_type : ntac unit :=
do gs ← get_goals,
  gt_str ← tactic_to_ntac (monad.sequence $ list.map infer_type gs),
  let t_str := list.map to_string gt_str,
  trace $ string.join t_str
meta def trace_proof (lang : nl) : ntac unit := 
do gt ← get_goal_tree,
trace $ goal_tree_to_format_nl lang gt

meta def trace_proof_html (lang : nl): ntac unit := 
do gt ← get_goal_tree,
trace $ goal_tree_to_format_nl_html lang gt
open io
meta def trace_proof_file (lang : nl) : ntac unit := 
do gt ← get_goal_tree,
dec ← decl_name,
fmt ← goal_tree_to_format_nl_html lang gt,
unsafe_run_io (do 
fd ← mk_file_handle ("out/"++dec.to_string++".js") mode.write,
fs.write fd (mk_buffer.append_string $ "ntachtml[\""++dec.to_string++"\"]=["++fmt.to_string++"]\n") 
),
trace $ goal_tree_to_format_nl_html lang gt

meta def trace_state : ntac unit := 
do gt ← get_goal_tree,
   s ← pp gt,
   s2 ← read2,
   trace $ s ++ "\n------\n" ++ (to_fmt s2)

meta def seq' (tac1 : ntac unit) (tac2 : ntac unit) : ntac unit :=
do g::gs ← get_goals,
   goal_trees_bak ← get_goal_tree,
   set_goals [g],
   unr ← mk_unres_goal_tree g,
   set_goal_tree unr,
   tac1,
   goal_tree1 ← get_goal_tree,
   gs ← get_goals,
   l ← getgoalinfos,
   goals ← get_goals,
   let gv:vector expr _ := ⟨goals, by refl⟩ in let vm := vector.map (λ e, tactic_to_ntac $ infer_type e) gv in 
   do goal_ti ← vector.sequence $ vm,
   let goal_trees := vector.map inf.unres gv in
   let goal_trees:vector goal_tree _:= vector.map₂ (λ inf0 ti, ⟨0, inf0, vector.nil, ti⟩) goal_trees goal_ti in
   do 
   set_goal_tree $ replc_unres g (λ ti, ⟨goals.length.succ, inf.andthen gv, vector.cons goal_tree1 goal_trees, ti⟩) goal_trees_bak,
   all_goals' tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

/--called by `;`-/
meta instance : has_andthen (ntac unit) (ntac unit) (ntac unit) := ⟨seq'⟩

end interactive
end ntac
