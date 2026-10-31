import LeanLab.Zhao2025.BScaledIntegral

/-!
The positive lambda0 scaling inequality in the proof of Lemma 2.3.
Source: Zhao 2025, displays 2.23 and 2.25, pages 6 and 7.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- Multiplication by exp of lambda t turns the positive lambda0 branch monotone. -/
theorem B_scaled_order (t l L l0 : ℝ) (ht : 0 ≤ t) (hl : 0 < l)
    (h0 : 0 < l0) (hL : l ≤ L) :
    Real.exp (l * t) * B t l l0 ≤ Real.exp (L * t) * B t L l0 := by
  rw [B_scaled_eq t l l0 hl h0, B_scaled_eq t L l0 (hl.trans_le hL) h0]
  have hpair (u : ℝ) (hu : 0 ≤ u) :
      Real.exp ((l + l0) * u) + Real.exp (-(l + l0) * u) ≤
        Real.exp ((L + l0) * u) + Real.exp (-(L + l0) * u) := by
    simpa using exp_pair_monotone (l + l0) (L + l0) 0 u (by linarith) le_rfl (by linarith) hu
  have hm1 :
      (∫ u in 0..t, Real.exp ((l + l0) * u) + Real.exp (-(l + l0) * u)) ≤
        ∫ u in 0..t, Real.exp ((L + l0) * u) + Real.exp (-(L + l0) * u) := by
    apply intervalIntegral.integral_mono_on ht
      ((by fun_prop : Continuous _).intervalIntegrable 0 t)
      ((by fun_prop : Continuous _).intervalIntegrable 0 t)
    intro u hu
    exact hpair u hu.1
  have hm2 : (∫ u in 0..t, (1 - Real.exp (-l0 * (t - u))) *
      (Real.exp (l * u) + Real.exp (-(l + 2 * l0) * u))) ≤
      ∫ u in 0..t, (1 - Real.exp (-l0 * (t - u))) *
        (Real.exp (L * u) + Real.exp (-(L + 2 * l0) * u)) := by
    apply intervalIntegral.integral_mono_on ht
      ((by fun_prop : Continuous _).intervalIntegrable 0 t)
      ((by fun_prop : Continuous _).intervalIntegrable 0 t)
    intro u hu
    have hk : 0 ≤ 1 - Real.exp (-l0 * (t - u)) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hu.2)]
    exact mul_le_mul_of_nonneg_left (exp_pair_monotone l L l0 u hl.le h0.le hL hu.1) hk
  have hm1' := mul_le_mul_of_nonneg_left hm1
    (by positivity : (0 : ℝ) ≤ 1 / 6 * Real.exp (-l0 * t))
  have hm2' := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ 1 / l0)
  unfold BScaled
  nlinarith only [hm1', hm2']

#print axioms B_scaled_order

end LeanLab.Zhao2025.Task56
