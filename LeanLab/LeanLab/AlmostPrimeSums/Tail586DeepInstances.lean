import LeanLab.AlmostPrimeSums.Tail586Deep

/-!
AI wrote this Lean code for CODEX task586. Goldbach is open.
A concrete nonempty sieve satisfies every hypothesis of the unbounded
cutoff Rankin weight construction. Source roles are in STATEMENTS.md.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real BoundingSieve

/-- The explicit Rankin regime is nonvacuous. The density sieve at
prime two works with z equal to four and D equal to four to the one
hundred. Derived instance for Iwaniec pp. 177 and 198. -/
theorem rankin_hypotheses_instance586 :
    ∃ s : BoundingSieve, s.prodPrimes = 2 ∧ 0 ≤ log 2 ∧ LinearDensity s (log 2) ∧
      ∃ z D : ℝ, 2 < z ∧ z ^ 10 ≤ D ∧
        (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) ∧
        4 + (2 * exp 2) * (1 + log 2 / log 2) *
          (log (log z / log 2) + log 2 / log 2) ≤ log D / log z := by
  obtain ⟨s, hP, _, hnu, hden, _⟩ := single_prime_density_instance
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  have hl4 : 0 < log 4 := log_pos (by norm_num)
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have hratio : log ((4 : ℝ) ^ 100) / log 4 = 100 := by
    rw [log_pow]
    field_simp
    norm_num
  have hM : log (log 4 / log 2) + log 2 / log 2 = log 2 + 1 := by
    rw [hlog4, mul_div_cancel_right₀ _ hl2.ne', div_self hl2.ne']
  have hA : 1 + log 2 / log 2 = 2 := by rw [div_self hl2.ne']; norm_num
  have he2 : exp 2 ≤ 9 := by
    have hh := pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_three.le 2
    norm_num at hh
    exact hh
  have hlog2 : log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hterm : exp 2 * (log 2 + 1) ≤ 18 := by
    have hh := mul_le_mul he2 (by linarith : log 2 + 1 ≤ 2) (by positivity)
      (by norm_num : (0 : ℝ) ≤ 9)
    norm_num at hh
    exact hh
  refine ⟨s, hP, hl2.le, hden, 4, (4 : ℝ) ^ 100, by norm_num, ?_, ?_, ?_⟩
  · exact pow_le_pow_right₀ (by norm_num) (by norm_num : 10 ≤ 100)
  · intro p hp
    have he : p = 2 := by simpa [hP, Nat.prime_two.primeFactors] using hp
    subst p
    norm_num
  · rw [hratio, hA, hM]
    nlinarith only [hterm]

end LeanLab.AlmostPrimeSums.Decomp1527b
