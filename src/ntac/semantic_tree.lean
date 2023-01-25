import ntac.sentence

meta inductive semantic_tree : Type
| assume_prop : string → semantic_tree → semantic_tree
| assume_val : string → string → semantic_tree → semantic_tree
| but_false : semantic_tree → semantic_tree
| assume_exist : string → semantic_tree → semantic_tree
| have_exact : string → string → semantic_tree → semantic_tree
| have_triv : string → semantic_tree → semantic_tree
| have_since : string → string → semantic_tree → semantic_tree
| suffice_exact : string → string → semantic_tree → semantic_tree
| suffice_from : string → semantic_tree → semantic_tree → semantic_tree
| exact : string → string → semantic_tree
| by_str : string → semantic_tree
| trivial : semantic_tree
| very_trivial : semantic_tree
| folded : sentence → list semantic_tree → semantic_tree
| following : semantic_tree → list semantic_tree → semantic_tree
| following_only : list semantic_tree → semantic_tree
| unresolved : semantic_tree
| contra : semantic_tree → semantic_tree

meta inductive proofdoc : Type
| mk : list (sentence×(option proofdoc)) → proofdoc

local attribute [instance] meta def inst: has_coe sentence (sentence×(option proofdoc)) := ⟨λ s:sentence, (s, none)⟩

namespace proofdoc
meta def tolistS (pd : proofdoc) : (list sentence) :=
let ⟨ret⟩ := pd in list.map prod.fst ret
end proofdoc

namespace semantic_tree

meta def to_proofdoc : semantic_tree → proofdoc := 
λ st, 
let fUN:semantic_tree → list (sentence×(option proofdoc)):= (λ s, (let ⟨ret⟩ := to_proofdoc s in ret)) in
match st with
| semantic_tree.unresolved := ⟨[S._unresolved]⟩
| semantic_tree.trivial := ⟨[S._trivial]⟩
| semantic_tree.very_trivial := ⟨[S._trivial]⟩
| semantic_tree.suffice_from e t1 t2 := ⟨fUN t1 ++ Adv._hence /a/ /i/ <V2VP>V2._suf_show <eNP>e :: fUN t2⟩
| semantic_tree.suffice_exact e1 e2 t := ⟨Adv._from <NP><eN>e1 /a/ /i/ <V2VP>V2._suf_show <eNP>e2 :: fUN t⟩
| semantic_tree.have_since e1 e2 t := ⟨Adv._since <NP><eN>e1 /a/ <eS>e2 ::fUN t⟩
| semantic_tree.have_triv e t2 := ⟨Adv._trivially /a/ <eS>e :: fUN t2⟩
| semantic_tree.assume_prop e t := ⟨/i/ <V2VP>V2._assume <eNP>e :: fUN t⟩
| semantic_tree.exact e1 e2 := ⟨[Adv._from <NP><eN>e1 /a/ <eS>e2]⟩
| semantic_tree.assume_val edef eval t := ⟨/i/ <V3VP> V3._let <NP><eN>edef <NP><eN>eval :: fUN t⟩
| semantic_tree.assume_exist e t := ⟨[S._trivial]⟩
| semantic_tree.have_exact e res t := ⟨Adv._from <NP><eN>e /a/ <eS>res :: fUN t⟩
| semantic_tree.folded s l := ⟨[(s, some ⟨list.join (list.map fUN l)⟩)]⟩
| semantic_tree.following s l := ⟨fUN s ++ list.join (list.map fUN l)⟩
| semantic_tree.following_only l := ⟨list.join (list.map fUN l)⟩
| semantic_tree.by_str s := ⟨[s]⟩
| _ :=⟨[S._trivial]⟩
end

meta def tolistS (s : semantic_tree) : (list sentence) := (to_proofdoc s).tolistS

end semantic_tree
