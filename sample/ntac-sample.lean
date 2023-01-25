import ntac

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin
  split,
  from hp,
  from hq
end

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin
  {split,
  {from hp},
  {from hq}}
end

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin
  {split,
  {exact hp},
  {exact hq}}
end

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] 
  split;{trace_expr p, assumption}
end
 
example (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin
split,
from or.inl hp,
from hq
end

example (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin
suffices hpr : p ∨ r,from ⟨hpr, hq⟩,
from or.inl hp,
end


theorem sample1 (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin[ntac] 
have hpr: p ∨ r, have aaa:true := dec_trivial,
from or.inl hp,
from ⟨hpr, hq⟩,
trace_proof LANG_en, trace_proof_file LANG_en
end

theorem sample2 (p q r: Prop) (hp : p) (hq : q) : (p ∨ r) ∧ q :=
begin[ntac] 
have hpr: p ∨ r,
NTAC_focus1_list {from or.inl hp} ["obviously, ",p ∨ r, ". "] tt tt,
from ⟨hpr, hq⟩,

end


example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] 
  NTAC_focus1_list {split} ["It suffices to show", p, " and ", q, " separately."] tt tt,
  NTAC_focus1_list {exact hp} ["we can use ", hp, " here."] tt tt,
  exact hq,
  trace_proof LANG_en, 
end

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] 
  NTAC_focus1_triv {split},
  exact hp,
  exact hq,
  trace_proof LANG_en, 
end


example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin[ntac] 
  NTAC_focus1_list {split} ["It suffices to show", p, " and ", q, " separately."] tt tt,
  TRIV, {exact hp} ,
  exact hq,
  trace_proof LANG_en, 
end
