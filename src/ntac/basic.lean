/-Basic tactics. Roughly corresponds to `init/meta/interactive.lean` . Some definitions are like copy-paste, and not so carefully designed.-/
import ntac.core
open tactic
open ntac
open interactive (parse)
open tactic.interactive
open interactive.types (texpr location using_ident with_ident_list only_flag ident_ pexpr_list_or_texpr)
open lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many
namespace ntac.interactive

meta def exact (q : parse texpr) : ntac unit :=
do tg ← getgoal1,
tgt : expr ← target,
   e ← i_to_expr_strict ``(%%q : %%tgt),
   tactic.exact e,
   kata ← infer_type e,
   replc_gi tg $ goal_tree.mk 0 (inf.exact e) vector.nil
meta def «from» := exact
meta def get_goal_tree_expr_list (goals : list(name × expr)): ntac (list goal_tree) :=
do goal ← goals.mfilter $ λ ⟨n, m⟩, bnot <$> (is_assigned m),
let goal_expr := list.map (λ nex:name × expr, nex.2) goal in
let goal_unres := list.map inf.unres goal_expr in
do goal_ti ← monad.sequence $ list.map (λ e, infer_type e) goal_expr,
return $ list.zip_with (λ i ti, ⟨0,i,vector.nil, ti⟩) goal_unres goal_ti 

private meta def concat_tags (tac : ntac (list (name × expr))) : ntac unit :=
let s := (do in_tag ← ↑get_main_tag,
      r ← tac,
      /- remove assigned metavars -/
      r ← r.mfilter $ λ ⟨n, m⟩, bnot <$> (is_assigned m),
      match r with
      | [(_, m)] := set_tag m in_tag /- if there is only new subgoal, we just propagate `in_tag` -/
      | _        := r.mmap' (λ ⟨n, m⟩, set_tag m (n::in_tag))
      end) in
mcond (tags_enabled)
  s
  (tac >> skip)

meta def assumption : ntac unit :=
do { ctx ←  local_context,
     tg ← getgoal1,
     t   ← target,
     H   ← find_same_type t ctx,
     ty ← infer_type H,
     replc_gi tg $ goal_tree.mk 0 (inf.assumption ty) vector.nil,
     tactic.exact H}
<|> fail "assumption tactic failed"

meta def simp (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag) (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
              (locat : parse location) (cfg : simp_config_ext := {}) : ntac unit := 
              do tg ← getgoal1,
              interactive.simp use_iota_eqn none no_dflt hs attr_names locat cfg,
              gs ← get_goals,
              match gs with
              | g::_ := do ti ← infer_type g, replc_gi tg $ goal_tree.mk 1 inf.simp $ vector.cons ⟨0, inf.unres g, vector.nil, ti⟩ vector.nil
              | _ := replc_gi tg $ goal_tree.mk 0 inf.simp_done vector.nil
              end

meta def rewrite (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit :=
 do tg ← getgoal1,
 interactive.rewrite q l cfg,
    gs ← get_goals,
              match gs with
              | g::_ := do ti ← infer_type g, replc_gi tg $ goal_tree.mk 1 inf.simp $ vector.cons ⟨0, inf.unres g, vector.nil, ti⟩ vector.nil
              | _ := replc_gi tg $ goal_tree.mk 0 inf.simp_done vector.nil
              end
meta def rw  (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) := rewrite q l cfg
--`meta def rw := rewrite` didn't work
meta def rwa (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) : ntac unit :=
rewrite q l cfg >> try assumption

meta def apply_mycore (e : expr) (cfg : apply_cfg := {}) : ntac (list (name × expr)) := 
do tg ← getgoal1,
  goals ← tactic.apply_core e cfg,
  glist ← get_goal_tree_expr_list goals,
  match glist with
  | [] := do trace "apply generated no goals", return goals
  | x::xs := do replc_gi tg $ goal_tree.mk (x::xs).length (inf.apply e) ⟨(x::xs),by refl⟩, return goals
  end

meta def tact_apply (e : expr) (cfg : apply_cfg := {}) : ntac (list (name × expr)) :=
do r ← apply_mycore e cfg,
   try_apply_opt_auto_param_for_apply cfg r,
   return r

meta def apply  (q : parse texpr) : ntac unit :=
concat_tags (do h ← i_to_expr_for_apply q, tact_apply h)
meta def tact_eapply (e : expr) : ntac (list (name × expr)) :=
apply_mycore e {new_goals := new_goals.non_dep_only}
meta def eapply (q : parse texpr) : ntac unit :=
concat_tags ((i_to_expr_for_apply q) >>= tact_eapply)

meta def by_cases : parse cases_arg_p → ntac unit
| (n, q) := concat_tags $ do
  tg ← getgoal1,
  p ← tactic.to_expr_strict q,
  tactic.by_cases p (n.get_or_else `h),
  pos_g :: neg_g :: rest ← get_goals,
  tipos ← infer_type pos_g,
  tineg ← infer_type neg_g,
  replc_gi tg $ goal_tree.mk 2 inf.bycase ⟨[⟨0, inf.unres pos_g, vector.nil, tipos⟩, ⟨0, inf.unres neg_g, vector.nil, tineg⟩],dec_trivial⟩,
  return [(`pos, pos_g), (`neg, neg_g)]

private meta def target' : tactic expr :=
target >>= instantiate_mvars >>= whnf

meta def split : ntac unit :=
do tg ← getgoal1,
[c] ← ↑(target' >>= get_constructors_for) | fail "split tactic failed, target is not an inductive datatype with only one constructor",
  k ← mk_const c,
goals ← apply_mycore k,
glist ← get_goal_tree_expr_list goals,
  match glist with
  | [] := fail "apply generated no goals"
  | x::xs := do replc_gi tg $ goal_tree.mk (x::xs).length (inf.apply tg) ⟨(x::xs),by refl⟩, concat_tags $ return goals
  end

meta def intro2_core (tg:expr) (n : name) : ntac expr :=
do e ← intro_core n,
 te ← infer_type e,
 ng ← getgoalinfo1,
 --set_goal_tree $ goal_tree.intro (n, te) ng,
replc_gi tg $ goal_tree.mk 1 (inf.intro (n, te)) ⟨[ng],dec_trivial⟩,
return e

meta def intro2(tg:expr) (n : name) : ntac expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then intro2_core tg n
   else whnf_target >> intro2_core tg n

meta def intro1  (tg:expr): ntac expr :=
intro2 tg `_

meta def propagate_tags (tac : ntac unit) : ntac unit :=
do tag ← get_main_tag,
   if tag = [] then tac
   else focus1 $ do
     tac,
     gs ← get_goals,
     when (bnot gs.empty) $ do
       new_tag ← get_main_tag,
       when new_tag.empty $ with_enable_tags (set_main_tag tag)

meta def intro (t: parse ident_?) : ntac unit := 
do tg ← getgoal1,match t with
| none     := propagate_tags (intro1 tg >> skip)
| (some h) := propagate_tags (intro2 tg h >> skip)
end

meta def assert (h : name) (t : expr) : ntac expr := 
do tg ← getgoal1,
e ← tactic.assert h t,
tg1::tg2::_ ← get_goals,
tgi1 ← mk_unres_goal_tree tg1,
tgi2 ← mk_unres_goal_tree tg2,
replc_gi tg $ goal_tree.mk 2 (inf.willhave ⟨h,t⟩) ⟨[tgi1, tgi2], dec_trivial⟩, return e

meta def assertv (h : name) (t : expr) (v : expr) : ntac expr := 
do tg ← getgoal1,
e ← tactic.assertv h t v,
tg1 ← getgoalinfo1,
replc_gi tg $ goal_tree.mk 1 (inf.have_ ⟨h,t,v⟩) ⟨[tg1],dec_trivial⟩, return e

meta def note (h : name) (t : option expr := none) (pr : expr) : ntac expr :=
let dv := λt, assertv h t pr in
option.cases_on t ((infer_type pr) >>= dv) dv

meta def have_aux (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac expr :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← i_to_expr e,
  v ← i_to_expr ``(%%p : %%t),
  assertv h t v
| none, some p := do
  p ←i_to_expr p,
  note h none p
| some e, none := (i_to_expr e) >>= assert h
| none, none := do
  u ←mk_meta_univ,
  e ← mk_meta_var (expr.sort u),
  assert h e
end

meta def «have» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac unit := 
do e ← have_aux h q₁ q₂, skip

meta def assert_swap (h : name) (t : expr) : ntac expr := 
do tg ← getgoal1,
e ← tactic.assert h t,
tactic.swap,
tg1::tg2::_ ← get_goals,
tgi1 ← mk_unres_goal_tree tg1,
tgi2 ← mk_unres_goal_tree tg2,
replc_gi tg $  goal_tree.mk 2 (inf.willhave ⟨h,t⟩) ⟨[tgi1,tgi2], dec_trivial⟩, return e

meta def suffice_aux  (h : parse ident?) (t : parse (tk ":" *> texpr)?) : ntac expr :=
let h := h.get_or_else `this in
match t with
| some e := (i_to_expr e) >>= assert_swap h
| none := do
  u ←mk_meta_univ,
  e ← mk_meta_var (expr.sort u),
  assert_swap h e
end

meta def «suffices» (h : parse ident?) (t : parse (tk ":" *> texpr)?) : ntac unit :=
do e ← suffice_aux h t,
skip
meta def definev (h : name) (t : expr) (v : expr) : ntac expr :=
do tg ← getgoal1,
e ← tactic.definev h t v,
tg1 ← getgoalinfo1,
replc_gi tg $ goal_tree.mk 1 (inf.define e v) ⟨[tg1],dec_trivial⟩, return e

meta def pose (h : name) (t : option expr := none) (pr : expr) : ntac expr :=
do tg ← getgoal1,
e ← tactic.pose h t pr,
tg1 ← getgoalinfo1,
replc_gi tg $ goal_tree.mk 1 (inf.define e pr) ⟨[tg1],dec_trivial⟩, return e

meta def define  (h : name) (t : expr) : ntac expr :=
do tg ← getgoal1,
e ← tactic.define h t,
tg1::tg2::_ ← get_goals,
tgi1 ← mk_unres_goal_tree tg1,
tgi2 ← mk_unres_goal_tree tg2,
replc_gi tg $ goal_tree.mk 2 (inf.willdefine e) ⟨[tgi1, tgi2],dec_trivial⟩, return e

meta def let_aux (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac expr :=
let h := h.get_or_else `this in
match q₁, q₂ with
| some e, some p := do
  t ← i_to_expr e,
  v ← i_to_expr ``(%%p : %%t),
  definev h t v
| none, some p := do
  p ← i_to_expr p,
  pose h none p
| some e, none := (i_to_expr e) >>= define h
| none, none := do
  u ← mk_meta_univ,
  e ← mk_meta_var (expr.sort u),
  define h e
end
meta def «let» (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : ntac unit :=
do e ← let_aux h q₁ q₂, skip

private meta def apply_num_metavars : expr → expr → nat → tactic expr
| f ftype 0     := return f
| f ftype (n+1) := do
  expr.pi m bi d b ← whnf ftype,
  a          ← mk_meta_var d,
  new_f      ← return $ f a,
  new_ftype  ← return $ b.instantiate_var a,
  apply_num_metavars new_f new_ftype n


meta def existsi_org (e : expr) : ntac unit :=
do tg ← getgoal1,
   [c]     ← tactic_to_ntac (target' >>= get_constructors_for) | fail "existsi tactic failed, target is not an inductive datatype with only one constructor",
   fn      ← mk_const c,
   fn_type ← infer_type fn,
   n       ←  get_arity fn,
   when (n < 2) (fail "existsi tactic failed, constructor must have at least two arguments"),
   t       ← apply_num_metavars fn fn_type (n - 2),
   tact_eapply (expr.app t e),
   t_type  ← tactic_to_ntac (infer_type t >>= whnf),
   e_type  ← infer_type e,
   (guard t_type.is_pi <|> fail "existsi tactic failed, failed to infer type"),
   (unify t_type.binding_domain e_type) <|> fail "existsi tactic failed, type mismatch between given term witness and expected type",
   skip
   --,replc_gi tg $ goal_tree.existsi e $ goal_tree.unres tg

meta def existsi : parse pexpr_list_or_texpr → ntac unit
| []      := return ()
| (p::ps) := (i_to_expr p) >>= existsi_org >> existsi ps

meta def by_contradiction (n : parse ident?) : ntac unit := tac1to1_inf (tactic.by_contradiction (n.get_or_else `h) $> ()) inf.contra
meta def by_contra (n : parse ident?) : ntac unit := by_contradiction n

end ntac.interactive