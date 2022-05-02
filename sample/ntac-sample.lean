import ntac

theorem sample1 (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin[ntac] 
have hpr: p ∨ r,
from or.inl hp,
from ⟨hpr, hq⟩,
trace_proof LANG_en, trace_proof_file LANG_en
end

theorem sample2 (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin[ntac] 
have hpr: p ∨ r,
SOL1p_str {from or.inl hp} "obviously, $p ∨ r$. ",
from ⟨hpr, hq⟩,
trace_proof LANG_en, trace_proof_file LANG_en
end
