/-
Quantitative convergence from the coefficient majorant used in Pintz Part I page 20 display 7.15.
The exponent three fourths comes from the proved local reciprocal totient estimate.
This is a helper bound and is not a rate asserted in the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp247a

namespace LeanLab.BhowmikGrimmelt2026

/-- A fixed reciprocal totient square majorant gives a finite coefficient tail estimate.
Source: helper for Pintz Part I page 20 display 7.15. -/
theorem aqZero247_finite_tail {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2))
    (Q M : ℕ) (hQ : 0 < Q) :
    ∑ q ∈ Finset.Ioc Q M, ‖aqZero247 χ₁ χ₂ N q‖ ≤
      (28 / 3 : ℝ) * C * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  by_cases hQM : Q ≤ M
  · calc
      _ ≤ ∑ q ∈ Finset.Ioc Q M, C * (7 * (q : ℝ) ^ (-(7 : ℝ) / 4)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos : 0 < q := lt_trans hQ (Finset.mem_Ioc.mp hq).1
        exact (hbound q hqpos).trans (mul_le_mul_of_nonneg_left
          (LeanLab.Zinoviev1997.inv_totient_sq_seven q hqpos) hC)
      _ = (C * 7) * ∑ q ∈ Finset.Ioc Q M, (q : ℝ) ^ (-(7 : ℝ) / 4) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (C * 7) * ((4 / 3 : ℝ) * (Q : ℝ) ^ (-(3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (LeanLab.Zinoviev1997.powerTail_Ioc Q M hQ hQM) (by positivity)
      _ = _ := by ring
  · rw [Finset.Ioc_eq_empty_of_le (by omega : M ≤ Q), Finset.sum_empty]
    positivity

/-- The same bound controls the infinite absolute tail.
Source: helper for Pintz Part I page 20 display 7.15. -/
theorem aqZero247_absolute_tail {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2))
    (Q : ℕ) (hQ : 0 < Q) :
    (∑' i : ℕ, ‖aqZero247 χ₁ χ₂ N (i + (Q + 1))‖) ≤
      (28 / 3 : ℝ) * C * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  apply Real.tsum_le_of_sum_range_le (fun i => norm_nonneg _)
  intro M
  have hinterval : Finset.Ioc Q (Q + M) = Finset.Ico (Q + 1) (Q + M + 1) := by
    ext q
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hshift : (∑ i ∈ Finset.range M, ‖aqZero247 χ₁ χ₂ N (i + (Q + 1))‖) =
      ∑ q ∈ Finset.Ioc Q (Q + M), ‖aqZero247 χ₁ χ₂ N q‖ := by
    rw [hinterval, Finset.sum_Ico_eq_sum_range,
      show Q + M + 1 - (Q + 1) = M by omega]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm (Q + 1) i]
  rw [hshift]
  exact aqZero247_finite_tail χ₁ χ₂ N C hC hbound Q (Q + M) hQ

/-- Truncating the generalized singular series after modulus Q has this explicit error.
The pointwise majorant is an explicit hypothesis, not an invoked OPEN leaf.
Source: helper for Pintz Part I page 20 display 7.15. -/
theorem aqZero247_truncation_error {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2))
    (Q : ℕ) (hQ : 0 < Q) :
    ‖genSing χ₁ χ₂ N - ∑ q ∈ Finset.range (Q + 1), aqZero247 χ₁ χ₂ N q‖ ≤
      (28 / 3 : ℝ) * C * (Q : ℝ) ^ (-(3 : ℝ) / 4) := by
  have hn := aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hbound
  have hs := hn.of_norm
  have hsplit := hs.sum_add_tsum_nat_add (Q + 1)
  rw [← aqZero247_tsum χ₁ χ₂ N hs, ← hsplit, add_sub_cancel_left]
  have htail : Summable (fun i : ℕ => ‖aqZero247 χ₁ χ₂ N (i + (Q + 1))‖) :=
    hn.comp_injective (fun i j hij => Nat.add_right_cancel hij)
  exact (norm_tsum_le_tsum_norm htail).trans
    (aqZero247_absolute_tail χ₁ χ₂ N C hC hbound Q hQ)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_finite_tail
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_absolute_tail
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_truncation_error
