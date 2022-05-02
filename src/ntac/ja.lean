import ntac.sentence

meta mutual def S_ja,NP_ja, N_ja, VP_ja, V_ja, V2_ja, V3_ja, Subj_ja, Adv_ja
with S_ja : S → string
| (S.AdvS adv s) := Adv_ja adv ++ "、" ++ S_ja s
| (S.AdvS' s adv) := Adv_ja adv ++ "、" ++ S_ja s
| (S.Expr e) := e
| (S.PredVP np vp) := NP_ja np ++ "は" ++ VP_ja vp
| S._trivial := "自明"
| S._unresolved := "NOT IMPLEMENTED"
| (S.Imp vp) := VP_ja vp
with NP_ja : NP → string
| (NP.EmbedS s) := S_ja s ++ "であること"
| (NP.UseN n) := N_ja n
with N_ja: N → string
| (N.Expr e) := e
with VP_ja : VP → string
| (VP.UseV v) := V_ja v
| (VP.UseV2 v2 np) := NP_ja np ++ "を" ++ V2_ja v2
| (VP.UseV3 v3 np1 np2) := NP_ja np1 ++ "を" ++ NP_ja np2 ++ "と" ++ V3_ja v3
with V_ja : V → string
| V.dummy := "(dummy)"
with V2_ja: V2 → string
| V2._suf_show := "示せば十分である"
| V2._assume := "仮定する"
with V3_ja: V3 → string
| V3._let := "する"
with Subj_ja : Subj → string
| Subj._if := "もし" -- λ s,"もし"++s++"とすれば"
with Adv_ja : Adv → string
| (Adv.Subjs subj s) := Subj_ja subj ++ S_ja s
| (Adv._from np):= NP_ja np ++ "より"
| Adv._hence := "したがって"
| Adv._from_assum := "仮定より"
| Adv._obviously := "明らかに"
| (Adv._since np):= NP_ja np ++ "より"

meta def LANG_ja : nl := {sentence_to_str := λ s, match s with | sentence.of_S s := S_ja s++"。" | sentence.of_str s := s end}

