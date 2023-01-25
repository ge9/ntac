import ntac
import data.nat.prime

open nat

notation n `!`:10000 := nat.factorial n
theorem exists_infinite_primes_tactic (n : ℕ) : ∃ p, n ≤ p ∧ nat.prime p :=
begin
let p := min_fac (n! + 1),
existsi p,
  have pp : nat.prime p, {
    have : n! + 1 ≠ 1,from (ne_of_gt $ succ_lt_succ $ factorial_pos n),
  from min_fac_prime this},
simp [pp],
{ apply le_of_not_ge,
  intro h,
  have h₁ : p ∣ n!,from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  from nat.prime.not_dvd_one pp h₂,
}
end

theorem exists_infinite_primes_ntac (n : ℕ) : ∃ p, n ≤ p ∧ nat.prime p :=
begin[ntac]
let p := min_fac (n! + 1),
  existsi p,
  have pp : nat.prime p, NTAC_focus1_list{
    have : n! + 1 ≠ 1, from (ne_of_gt $ succ_lt_succ $ factorial_pos n),
     from min_fac_prime this} ["", p, " is prime. "] tt tt,
  simp [pp],
  { apply le_of_not_ge, 
    intro h, 
    have h₂ : p ∣ 1, {have h₁ : p ∣ n!, TRIV, from dvd_factorial (min_fac_pos _) h,
    TRIV, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _) },
    
    NTAC_focus1_str{from nat.prime.not_dvd_one pp h₂}"This is contradiction. " tt tt}, 
  trace_state,trace_proof_file LANG_en
end


