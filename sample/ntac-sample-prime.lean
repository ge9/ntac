import ntac
import data.nat.prime

open nat

notation n `!`:10000 := nat.factorial n

theorem exists_infinite_primes_tactic (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
begin
let p := min_fac (n! + 1),
existsi p,
  have pp : prime p, {
    have : n! + 1 ≠ 1,from (ne_of_gt $ succ_lt_succ $ factorial_pos n),
  from min_fac_prime this},
simp [pp],
{ apply le_of_not_ge,
  intro h,
  have h₁ : p ∣ n!,from dvd_factorial (min_fac_pos _) h,
  have h₂ : p ∣ 1, from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
  from prime.not_dvd_one pp h₂,
}
end

theorem exists_infinite_primes_ntac (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
begin[ntac]
let p := min_fac (n! + 1),
  existsi p,
  have pp : prime p, {
    have : n! + 1 ≠ 1, TRIV, from (ne_of_gt $ succ_lt_succ $ factorial_pos n),
    TRIV, from min_fac_prime this},
  simp [pp],
  { apply le_of_not_ge, 
    intro h,
    have h₂ : p ∣ 1, {have h₁ : p ∣ n!, TRIV, from dvd_factorial (min_fac_pos _) h,
    SOL1p_str{from (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _)} "Since $p ∣ n! + 1$, $p ∣ 1$"},
    SOL1p_str{from prime.not_dvd_one pp h₂}"However, this is contradiction" }, 
  trace_state,trace_proof_file LANG_en
end


