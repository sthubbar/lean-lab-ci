import LeanLab.Pintz2021.MinorArcs

/-!
The power-of-two exponential sum in P0054 page 13 display 4.1.
The natural cutoff K is floor Lnu X when used in the paper.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.PowersTask99

open Finset MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

/-- Display 4.1 with an explicit natural exponent cutoff. -/
noncomputable def G (K : ℕ) (α : ℝ) : ℂ :=
  ∑ ν ∈ Icc 1 K, e (((2 ^ ν : ℕ) : ℝ) * α)

/-- The power sum has norm at most its number of terms. -/
theorem norm_G_le (K : ℕ) (α : ℝ) : ‖G K α‖ ≤ K := by
  unfold G
  calc
    _ ≤ ∑ ν ∈ Icc 1 K, ‖e (((2 ^ ν : ℕ) : ℝ) * α)‖ := norm_sum_le _ _
    _ = K := by simp only [norm_e, sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num

/-- Orthogonality gives the exact second moment of the power sum. -/
theorem second_moment (K : ℕ) :
    ∫ α in (-(1 / 2 : ℝ))..(1 / 2), ‖G K α‖ ^ 2 = (K : ℝ) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpt : ∀ α : ℝ, ((‖G K α‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ Icc 1 K, ∑ b ∈ Icc 1 K,
        e ((((2 : ℤ) ^ a - (2 : ℤ) ^ b : ℤ) : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj', G, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [← e_neg, ← e_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  have hc : ∀ a b : ℕ, Continuous (fun α : ℝ =>
      e ((((2 : ℤ) ^ a - (2 : ℤ) ^ b : ℤ) : ℝ) * α)) := fun a b => continuous_e_mul _
  rw [intervalIntegral.integral_finsetSum (fun a _ =>
    (continuous_finsetSum _ (fun b _ => hc a b)).intervalIntegrable _ _)]
  have hdiag : ∀ a b : ℕ, (2 : ℤ) ^ a - (2 : ℤ) ^ b = 0 ↔ a = b := by
    intro a b
    rw [sub_eq_zero]
    exact pow_right_inj₀ (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≠ 1)
  calc
    _ = ∑ a ∈ Icc 1 K, (1 : ℂ) := by
      apply sum_congr rfl
      intro a ha
      rw [intervalIntegral.integral_finsetSum (fun b _ => (hc a b).intervalIntegrable _ _)]
      simp_rw [integral_e_int]
      simp [hdiag, ha]
    _ = (K : ℂ) := by simp

/-- The absolute integral step in display 4.6 on a finite-measure subset. -/
theorem weighted_integral_le (S : ℝ → ℂ) {E : Set ℝ} (hE : volume E < ⊤)
    {B : ℝ} (hB : 0 ≤ B) (hS : ∀ α ∈ E, ‖S α‖ ≤ B) (K k : ℕ) (m : ℤ) :
    ∫ α in E, ‖S α ^ 2 * G K α ^ k * e (-(m : ℝ) * α)‖ ≤
      B ^ 2 * (K : ℝ) ^ k * volume.real E := by
  have hpt : ∀ α ∈ E,
      ‖S α ^ 2 * G K α ^ k * e (-(m : ℝ) * α)‖ ≤ B ^ 2 * (K : ℝ) ^ k := by
    intro α hα
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_e, mul_one]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (hS α hα) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_G_le K α) k)
      (pow_nonneg (norm_nonneg _) k) (pow_nonneg hB 2)
  have hb := norm_setIntegral_le_of_norm_le_const
    (f := fun α => ‖S α ^ 2 * G K α ^ k * e (-(m : ℝ) * α)‖) hE
    (fun α hα => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpt α hα)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)

end LeanLab.Pintz2021.PowersTask99

#print axioms LeanLab.Pintz2021.PowersTask99.norm_G_le

#print axioms LeanLab.Pintz2021.PowersTask99.second_moment

#print axioms LeanLab.Pintz2021.PowersTask99.weighted_integral_le
