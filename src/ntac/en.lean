import ntac.sentence
infix `+++`:65 := λ a b,a++" "++b
meta mutual def S_en,NP_en, N_en, VP_en, V_en, V2_en, V3_en, Subj_en, Adv_en
with S_en : S → string
| (S.AdvS adv s) := Adv_en adv ++ ", " ++ S_en s
| (S.AdvS' s adv) := Adv_en adv ++ ", " ++ S_en s
| (S.Expr e) := e
| (S.PredVP np vp) := NP_en np +++ VP_en vp
| S._trivial := "trivial"
| S._unresolved := "(unresolved, may be solved by unsupported tactics)"
| (S.Imp vp) := VP_en vp
with NP_en : NP → string
| (NP.EmbedS s) := S_en s
| (NP.UseN n) := N_en n
with N_en: N → string
| (N.Expr e) := e
with VP_en : VP → string
| (VP.UseV v) := V_en v
| (VP.UseV2 v2 np) := V2_en v2 +++ NP_en np
| (VP.UseV3 v3 np1 np2) := V3_en v3 +++ NP_en np1 ++" be " ++ NP_en np2
with V_en : V → string
| V._hold := "holds"
with V2_en: V2 → string
| V2._suf_show := "it suffices to show"
| V2._assume := "assume"
with V3_en: V3 → string
| V3._let := "let"
with Subj_en : Subj → string
| Subj._if := "if"
with Adv_en : Adv → string
| (Adv.Subjs subj s) := Subj_en subj +++ S_en s
| (Adv._from np):= "from"+++NP_en np
| Adv._hence := "hence"
| Adv._from_assum := "from assumption"
| Adv._trivially := "trivially"
| (Adv._since np):= "since"+++NP_en np

meta def capitalize (s: string):=
match s.to_list with
| c::cs := let v := c.val in (if (0x61 <= v ∧ v <= 0x7A) then char.of_nat (v-0x20)::cs else c::cs).as_string
| _ := s
end

meta def LANG_en : nl :=  {sentence_to_str := λ s, match s with | sentence.of_S s := capitalize (S_en s)++".  " | sentence.of_str s := s end}
