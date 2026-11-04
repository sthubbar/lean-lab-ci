/-
The zero endpoint of the locally encoded singular series lower bound.
Source: P0029 page 6 display 2.9. The paper discusses positive even integers.
The local leaf also quantifies over zero. Its statement is left unchanged.
This is a local endpoint refutation, not a refutation of the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Audit1610

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- The defining singular series at zero is divergent and Lean's totalized sum is zero. -/
theorem singular_zero261 : singular 0 = 0 := by
  let f : ℕ → ℝ := fun q =>
    (((moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2) * (ramanujan q 0).re
  have hpval (p : ℕ) (hp : p.Prime) : f p = 1 / (Nat.totient p : ℝ) := by
    dsimp [f]
    have hz : (ramanujan p (0 : ℤ)).re = (Nat.totient p : ℝ) := by
      simpa only [Nat.cast_zero] using Audit1610.ramanujan_prime_zero p
    rw [moebius_apply_prime hp, hz]
    have hφ : (Nat.totient p : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
    norm_num
    field_simp
  have hnot : ¬ Summable f := by
    intro hf
    apply not_summable_one_div_on_primes
    apply Summable.of_nonneg_of_le (fun n => Set.indicator_nonneg (fun p _ => by positivity) n)
      (fun n => ?_) hf.norm
    by_cases hp : n.Prime
    · have hmem : n ∈ {p : ℕ | p.Prime} := hp
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, hpval n hp]
      rw [abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le
        (by exact_mod_cast Nat.totient_pos.mpr hp.pos) (by exact_mod_cast Nat.totient_le n)
    · have hmem : n ∉ {p : ℕ | p.Prime} := hp
      rw [Set.indicator_of_notMem hmem]
      exact norm_nonneg _
  exact tsum_eq_zero_of_not_summable hnot

/-- The local lower bound with every even natural integer fails at zero. -/
theorem not_singular_lower_all_even261 :
    ¬ (∀ N : ℕ, Even N → (1 : ℝ) ≤ singular N) := by
  intro h
  have hzero := h 0 (by exact ⟨0, by norm_num⟩)
  rw [singular_zero261] at hzero
  norm_num at hzero

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.singular_zero261
#print axioms LeanLab.BhowmikGrimmelt2026.not_singular_lower_all_even261
