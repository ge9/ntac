--Reference: https://www.grammaticalframework.org/lib/doc/synopsis/index.html

meta mutual inductive S, NP, N, VP, V, V2, V3, Subj, Adv
with S : Type
| AdvS : Adv → S → S
| AdvS' : S → Adv → S
| Expr : string → S
| PredVP : NP → VP → S
| _trivial : S
| _unresolved : S
| Imp : VP → S
with NP : Type
| EmbedS : S → NP
| UseN : N → NP
with N: Type
| Expr : string → N
with VP : Type
| UseV : V → VP
| UseV2 : V2 → NP → VP
| UseV3 : V3 → NP → NP → VP
with V : Type
| dummy: V -- currently no intransitive verb 
with V2: Type
| _suf_show : V2
| _assume : V2
with V3: Type
| _let : V3
with Subj : Type
| _if : Subj
with Adv : Type
| Subjs : Subj → S → Adv
| _from : NP → Adv
| _hence : Adv
| _from_assum : Adv
| _obviously : Adv
| _since : NP → Adv
infix `/a/`:140 := S.AdvS
infix `/aa/`:140 := S.AdvS'
infix `/p/`:160 := S.PredVP
prefix `/i/`:110 := S.Imp
infix `/s/`:150 := Adv.Subjs
prefix `<eNP>`:200 := λ e, NP.EmbedS (S.Expr e)
prefix `<eN>`:200 := N.Expr
prefix `<NP>`:190 := NP.UseN
prefix `<eS>`:200 := S.Expr
prefix `<VVP>`:300 := VP.UseV
prefix `<V2VP>`:300 := VP.UseV2
prefix `<V3VP>`:300 := VP.UseV3
meta inductive sentence : Type 
| of_str : string → sentence
| of_S : S → sentence
meta instance sentence_of_str: has_coe string sentence := ⟨λ s, sentence.of_str s⟩
meta instance sentence_of_S: has_coe S sentence := ⟨λ s, sentence.of_S s⟩

meta structure nl := (sentence_to_str : sentence → string)
meta def listS_to_str (l: nl) (lsent: list sentence) : string :=
string.intercalate "\n" $ list.map l.sentence_to_str lsent
--the precedence of ++ is 65
--the precedence of :: is 67
