import ntac.semantic_tree
import ntac.ja
import ntac.en
import ntac.katex
import data.vector
import init.data.to_string

meta structure named_expr := (name: name) (type: expr)
meta structure named_expr_value := (name: name) (type: expr) (value: expr)

/--The types of inferences. The natural number indicates how many sub-inferences are needed to construct the inference. See also the definition of `goal_tree`. -/
meta inductive inf : ℕ → Type
/-- unresolved goals-/
| unres : expr → inf 0
--| unres_andthen : expr → inf 0 -- unused

| fold_auto : inf 1
/--the first represents the content of {}, and remaining n goals represents the remaining goals.-/
| willbeNgoal_str : option (string × bool) → ∀{n: ℕ}, inf (n.succ)
/--technical component; "closed" subgoals in willbeNgoal_str.-/
| unsupported : ∀{n: ℕ}, inf (n.succ)
| closed : inf 0

--for miscellaneous tactics
/--give exact formula-/
| exact : expr → inf 0
| assumption : expr → inf 0
| rewrite : inf 1
--| simp2 : (list expr) → inf 1
| simp : inf 1
| simp_done : inf 0
| skip : inf 1
| intro : (name × expr) → inf 1
| have_ : named_expr_value → inf 1
| define : expr → expr → inf 1
| willhave : named_expr → inf 2
| willdefine : expr → inf 2
| suffice : named_expr → inf 2
| admit : inf 0 --"sorry" tactic
-- | done : inf 0 -- unused
/--mark a goal as trivial-/
--| triv : inf 1
| contra : inf 1 -- contradiction
| existsi : expr → inf 1
| bycase:inf 2
| andthen {n: ℕ} : vector expr n → inf n.succ
| apply {n: ℕ}: expr → inf n.succ

/-- Recursive data structure representing inference (process of tactic execution).  `g` represents sub-inferences. `ti` represent the type of the goal that `i` proves.
`n` may not be implicit because pattern match with underscore seems to fail.-/
meta inductive goal_tree : Type
| mk (n : ℕ) (i : inf n) (g : vector goal_tree n) (ti : expr) : goal_tree

meta def goal_tree.get_ti (goal_tree:goal_tree):= let⟨_,_,_,ti⟩ := goal_tree in ti

namespace vector
def second {α} {n} (v: vector α (nat.succ (nat.succ n))): α := v.tail.head 
universes u v
def sequence' {m : Type u → Type v} [monad m] {α : Type u} : ∀ (nn : ℕ), vector (m α) nn → m (vector α nn)
    | 0 ⟨[],h⟩       := return ⟨[],h⟩
    | (nat.succ nn) ⟨h::t, prf⟩ := do h' ← h, t' ← sequence' nn ⟨t,congr_arg nat.pred prf⟩, return $ vector.cons h' t'
/--`monad.sequence` for `vector`, not `list`-/
def sequence {nn : ℕ } {m : Type u → Type v} [monad m] {α : Type u} : vector (m α) nn → m (vector α nn) := sequence' nn
end vector

/--A recursive function that replaces `goal_tree` of an unresolved goal (`expr`) with another tree-/
meta def replc_unres : expr → goal_tree → ( (expr → goal_tree) → goal_tree) :=
λ e oldg, 
match oldg with
| ⟨0, (inf.unres ex),_, ti⟩ := if e=ex then λ newg,newg ti else λ_,oldg
--| ⟨0,  (inf.unres_andthen ex),_, ti⟩ := if e=ex then newg ti else oldg
| ⟨n, i, g, t⟩ :=  λ newg, ⟨n, i, vector.map (λ gt, (replc_unres e) gt newg) g, t⟩
end

meta instance str_tac_str: has_coe string (tactic string) := ⟨pure⟩
meta def expr_to_tac_str (e: expr): tactic string := do ppe ← tactic.pp e, return ppe.to_string
meta instance expr_tac_str : has_coe expr (tactic string) := ⟨expr_to_tac_str⟩
meta def expr_raw_str (e: expr): tactic string := pure e.to_string

meta def join_tstr (ts1 : tactic string) (ts2 : tactic string) : tactic string := do 
s1 ← ts1, s2 ← ts2, return (s1++s2)

local infix `<T>`:65 := join_tstr
/--debug function. Not so useful.-/
meta instance aaa : has_coe string (tactic format) := ⟨return ∘ to_fmt⟩
meta def goal_tree_to_string : goal_tree → tactic string :=
let goal_tree_to_string3: goal_tree → tactic string := λ gi, let⟨_, _, _, ty⟩ := gi in do ty ← tactic.pp ty,g ← (goal_tree_to_string gi),return $ "("++ty.to_string++"::" ++g++")" in
λ g, 
let ppstr := ((λ (e:expr), do ppe ← tactic.pp e, pure $ to_string ppe) : expr → tactic string) in
let li: list(tactic string) := match g with
| ⟨0, inf.unres e, _, _⟩ := [" *unres* :", ↑e]
--| ⟨0, inf.unres_andthen e, _, _⟩ := [" *unres andthen* :", expr_raw_str e]
| ⟨0, inf.admit, _, _⟩ := ["sorry"]
| ⟨1, inf.intro ⟨n, e⟩, gg, ti⟩ := ["INTRO ", to_string n, ":", ↑e, "(" , (goal_tree_to_string gg.head) , ")"]
| ⟨1, inf.have_ ⟨name, type, val⟩, gg, _⟩ := ["have " , ppstr type , " , by <", ppstr val , ">\nand\n<" , (goal_tree_to_string gg.head) , ">"]
| ⟨1, inf.define edef eval, gg, _⟩  := ["let ", ↑edef <T>" := [<" , ↑eval , ">and<" , (goal_tree_to_string gg.head) , ">"]
| ⟨2, inf.willhave ⟨name, type⟩ ,gg, _ ⟩ := ["will have " , ↑type <T>" from<" , (goal_tree_to_string gg.head) , ">and<" , (goal_tree_to_string gg.second) , ">"]
| ⟨2,inf.suffice ⟨name, type⟩, gg, _⟩ := ["suffice " , ↑type <T>" from<" , (goal_tree_to_string gg.head) , ">and<" , (goal_tree_to_string gg.second) , ">"]
| ⟨2,inf.willdefine e,gg,_⟩ := ["will let" , ↑e , "by<" , (goal_tree_to_string gg.head) , ">and<" , (goal_tree_to_string gg.second) , ">"]
--| ⟨2,inf.willadd1goal_str s,gg,_⟩ := ["!!!!!will add1 \"" , s , "\" by <" , (goal_tree_to_string gg.head) , ">cont<", (goal_tree_to_string gg.second),">!!!!"]
| ⟨nat.succ n,inf.willbeNgoal_str d,gg,_⟩ := let st := (match d with | some (s, tt) := s | some (s, ff) := "("++s++")" | _ := "triv" end) in ["!!!!!will add1 \"" , st , "\" by <" , (goal_tree_to_string gg.head) , ">cont<", 
        (do v ← vector.sequence (vector.map goal_tree_to_string gg.tail), pure (string.intercalate ", " (v.to_list))),">!!!!"]
| ⟨nat.succ n,inf.unsupported,gg,_⟩ := ["unsupported. by <" , (goal_tree_to_string gg.head) , ">cont<", 
        (do v ← vector.sequence (vector.map goal_tree_to_string gg.tail), pure (string.intercalate ", " (v.to_list))),">!!!!"]
-- | ⟨0, inf.done, _, _⟩  := ["done"]
| ⟨0, inf.closed, _, _⟩:= ["(CONT)"]
| ⟨0, inf.exact e, _, _⟩:= ["exact " , ↑e]
--| ⟨1, inf.triv, gg, _⟩:= ["triv (" , goal_tree_to_string gg.head , ")"]
| ⟨1, inf.fold_auto, gg, _⟩:= ["fold_auto (" , goal_tree_to_string gg.head , ")"]
| ⟨1, inf.existsi e,gg,_⟩:= ["exists (" , ↑e , "and indeed" , goal_tree_to_string gg.head , ")"]
| ⟨0, inf.assumption e,_, _⟩:= ["assumption " , ↑e]
| ⟨1, inf.contra, gg, _⟩ := ["contradiction (" , goal_tree_to_string gg.head , ")"]
| ⟨1, inf.rewrite, gg, _⟩ := ["rw (" , goal_tree_to_string gg.head , ")"]
--| ⟨1, inf.simp2 ln, gg, _⟩:= ["simp by ", string.join (list.map to_string ln) , "(" , goal_tree_to_string gg.head , ")" ]
| ⟨1, inf.simp, gg, _⟩ := ["simp (" , goal_tree_to_string gg.head , ")" ]
| ⟨0, inf.simp_done, _, _⟩ := ["by simp" ]
| ⟨1, inf.skip, gg, _⟩:= ["skip (" , goal_tree_to_string gg.head , ")"]
| ⟨n, inf.apply ee, gg, _⟩ := 
let sl := list.map goal_tree_to_string3 gg.to_list in
["apply <" , ↑ee, "> and from["] ++ sl.intersperse ", " ++ ["]"]
| ⟨2, inf.bycase,gg,_⟩ := 
let sl := list.map goal_tree_to_string3 gg.to_list in
["bycase["] ++ sl.intersperse ", " ++ ["]"]
| ⟨n, inf.andthen el,gg,_⟩ :=
let str1 := goal_tree_to_string gg.head in
let sl := vector.map₂ (λ a b, (["(", ↑a , " → ", (goal_tree_to_string b), ")"]:list (tactic string))) el gg.tail in
(["do {", str1, "} and then{"]: list (tactic string)) ++ list.intercalate [", "] sl.to_list ++ ["}"]
end
in 
let seq := monad.sequence li
in do s ← seq, return $ string.join s

/--one of main functions of this library, but contains only a few, ad-hoc conversion-/
meta def goal_tree_to_semantic_tree : goal_tree → tactic semantic_tree := 
λ g, let getstr (e:expr) := do str ← expr_to_katex e, return $ "$"++str++"$" in
do match g with
| ⟨0, inf.unres _, _, _⟩ := pure semantic_tree.unresolved
--| ⟨0, inf.unres_andthen _, _, _⟩ := pure semantic_tree.unresolved
| ⟨0, inf.admit, _, _⟩ := pure semantic_tree.unresolved
| ⟨1, inf.intro ⟨n, e⟩, gg, ti⟩ := pure semantic_tree.assume_prop <*> getstr e <*> goal_tree_to_semantic_tree gg.head
| ⟨1, inf.have_ ⟨n,t,v⟩, gg, _⟩ := pure semantic_tree.have_exact <*> getstr v <*> getstr t <*> goal_tree_to_semantic_tree gg.head
| ⟨1, inf.define edef eval, gg, _⟩ := pure semantic_tree.assume_val <*> getstr edef <*> getstr eval <*> goal_tree_to_semantic_tree gg.head
| ⟨2, inf.willhave ⟨n,t⟩ ,gg, _ ⟩:= 
    match gg.head with
    | ⟨1, inf.willbeNgoal_str none ,_,_⟩ := pure semantic_tree.have_triv <*> getstr t <*>(goal_tree_to_semantic_tree gg.second) 
    | ⟨1, inf.fold_auto ,g,_⟩ := pure semantic_tree.following <*> (pure semantic_tree.folded <*> (do e ← getstr t, pure $ sentence.of_S $ <NP><eN>e /p/ <VVP>V._hold) <*> monad.sequence [(goal_tree_to_semantic_tree g.head)] ) <*> monad.sequence [goal_tree_to_semantic_tree gg.second]
    | ⟨0, inf.exact e, _, ta⟩ := pure semantic_tree.have_exact <*> getstr e <*> getstr ta <*> (goal_tree_to_semantic_tree gg.second) 
    | ⟨2, inf.willhave _, ⟨⟨1, inf.willbeNgoal_str none ,_,t1⟩::⟨1, inf.willbeNgoal_str none ,_,t2⟩::_,_⟩, ta⟩ := 
     pure semantic_tree.have_since <*> getstr t1  <*> getstr t2 <*> (goal_tree_to_semantic_tree gg.second)
    | _   := pure semantic_tree.following <*> (goal_tree_to_semantic_tree gg.head) <*> monad.sequence [goal_tree_to_semantic_tree gg.second]
    end
| ⟨2,inf.suffice ⟨_,t⟩, gg, _⟩ := pure semantic_tree.suffice_from <*> getstr t <*> (goal_tree_to_semantic_tree gg.head) <*> (goal_tree_to_semantic_tree gg.second) 
| ⟨2,inf.willdefine ne,gg,_⟩ := pure semantic_tree.following <*> (goal_tree_to_semantic_tree gg.head) <*> monad.sequence [goal_tree_to_semantic_tree gg.second]
| ⟨nat.succ n,inf.willbeNgoal_str d,gg,_⟩ := 
do cont ← goal_tree_to_semantic_tree gg.head,
   contlist ← monad.sequence $ list.map goal_tree_to_semantic_tree gg.tail.to_list,
   match d with
    | some (s, tt) := return $ semantic_tree.following ((semantic_tree.folded (sentence.of_str s)) [cont]) contlist
    | some (s, ff) := return $ semantic_tree.following (semantic_tree.by_str s) contlist 
    | _ := return $ semantic_tree.following_only contlist
        end 
| ⟨nat.succ n,inf.unsupported,gg,_⟩ := 
do cont ← goal_tree_to_semantic_tree gg.head,
   contlist ← monad.sequence $ list.map goal_tree_to_semantic_tree gg.tail.to_list,
   return $ semantic_tree.following (semantic_tree.by_str "(used unsupported tactic here.)") contlist 
 
| ⟨0, inf.closed, _, t⟩ := pure $ semantic_tree.by_str "(closed)" --TEMP:消す

-- | ⟨0, inf.done, _, _⟩ := pure semantic_tree.unresolved
| ⟨0, inf.exact e, _, t⟩ := pure semantic_tree.exact <*> getstr e <*> getstr t
--| ⟨1, inf.triv, _, _⟩ := pure semantic_tree.trivial
| ⟨1, inf.fold_auto, _, _⟩ := pure semantic_tree.very_trivial
| ⟨1, inf.existsi e,gg,_⟩ :=pure semantic_tree.assume_exist <*> getstr e <*> goal_tree_to_semantic_tree gg.head
| ⟨0, inf.assumption e,_, t⟩ := pure semantic_tree.exact <*> getstr e <*> getstr t
| ⟨1, inf.contra, gg, _⟩ := pure semantic_tree.contra <*> goal_tree_to_semantic_tree gg.head
| ⟨1, inf.rewrite, gg, _⟩ := pure semantic_tree.unresolved
--| ⟨1, inf.simp2 ln, gg, _⟩ := pure semantic_tree.unresolved
| ⟨0, inf.simp_done, _, _⟩ := pure semantic_tree.trivial
| ⟨1, inf.simp, gg, _⟩ := goal_tree_to_semantic_tree gg.head
| ⟨1, inf.skip, gg, _⟩ := goal_tree_to_semantic_tree gg.head
| ⟨n, inf.apply ee, gg, ti⟩ := 
match ee with
    | `(Exists.intro %%n) := match ti with | `(Exists %%d) := if (expr.binding_name d) = expr.local_pp_name n then goal_tree_to_semantic_tree gg.head else pure semantic_tree.trivial |_:= pure semantic_tree.trivial end
    --|`(and.intro) := pure semantic_tree.trivial
    | e := match ti with 
            --| `(and %%a %%b) :=  pure semantic_tree.unresolved
            | _ := if n = 1 then pure semantic_tree.suffice_exact <*> getstr e <*> getstr gg.head.get_ti <*> goal_tree_to_semantic_tree gg.head else 
            do eo ← tactic.pp e, tactic.trace e.to_string, pure semantic_tree.unresolved
           end
    end
| ⟨n, inf.bycase,_,_⟩ := pure semantic_tree.unresolved
| ⟨n, inf.andthen _,_,_⟩ := pure semantic_tree.unresolved
end

meta def goal_tree_to_format : goal_tree → tactic format  := λ g, do str ← goal_tree_to_string g, return $ to_fmt str
meta def goal_tree_to_format_nl (lang : nl) : goal_tree → tactic format := λ g, do semtree ← goal_tree_to_semantic_tree g,return $ listS_to_str lang semtree.tolistS
meta instance : has_to_tactic_format goal_tree := ⟨goal_tree_to_format⟩

meta def goal_tree_to_format_nl_html  (lang : nl)  : goal_tree → tactic format := 
λ g, 
do semtree ← goal_tree_to_semantic_tree g,
let ⟨l⟩ := semtree.to_proofdoc in
let nak := 
list.map 
(λ s,
let ((st, opd): sentence×(option proofdoc)) := s in
match opd with
| none := "\""++(lang.sentence_to_str st).replace_char '\n' " " ++"\""
| some pd := "{sur: \""++(lang.sentence_to_str st).replace_char '\n' " " ++"\", con: \""++("".intercalate $ list.map lang.sentence_to_str pd.tolistS).replace_char '\n' "\\n" ++"\"}"
end)
l
in
return $ ", \n".intercalate nak