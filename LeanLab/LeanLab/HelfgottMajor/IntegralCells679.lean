import Mathlib

/-!
Monotone upper sums for the logarithmic weight integral on P0014 page 35.
The derivative test replaces the numerical convexity assertions in the existing leaf notes.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.IntegralCells679
open Real Set

/-- P0014 page 35 after display 4.12, derived monotonicity of its log squared weight. -/
theorem log_sq_weight_antitone :
    AntitoneOn (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) (Ici 0) := by
  have hd (v : ℝ) (hv : 9 / 4 ≤ v) :
      HasDerivAt (fun u : ℝ => Real.log u ^ 2 / (u - 2))
        ((2 * Real.log v / v * (v - 2) - Real.log v ^ 2) / (v - 2) ^ 2) v := by
    have h := ((Real.hasDerivAt_log (show v ≠ 0 by linarith)).pow 2).div
      ((hasDerivAt_id v).sub_const 2) (show v - 2 ≠ 0 by linarith)
    convert h using 1 <;> simp <;> try ring
    all_goals
      funext u
      simp [Pi.div_apply, Pi.pow_apply, div_eq_mul_inv]
  have hanti : AntitoneOn (fun u : ℝ => Real.log u ^ 2 / (u - 2)) (Ici (9 / 4)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    intro v hv
    have hv0 : (0 : ℝ) < v := by have := interior_subset hv; simp only [mem_Ici] at this; linarith
    have hv2 : 2 < v := by have := interior_subset hv; simp only [mem_Ici] at this; linarith
    rw [(hd v (interior_subset hv)).deriv]
    have hl := Real.le_log_one_add_of_nonneg (show 0 ≤ v - 1 by linarith)
    have he : (1 : ℝ) + (v - 1) = v := by ring
    rw [he] at hl
    have hrat : 2 * (v - 2) / v ≤ 2 * (v - 1) / (v - 1 + 2) := by
      rw [div_le_div_iff₀ hv0 (by linarith)]
      nlinarith
    have hlog : 2 * (v - 2) / v ≤ Real.log v := hrat.trans hl
    have hL0 : 0 ≤ Real.log v := Real.log_nonneg (by linarith)
    have hnum : 2 * Real.log v / v * (v - 2) - Real.log v ^ 2 ≤ 0 := by
      have hmul := mul_le_mul_of_nonneg_left hlog hL0
      nlinarith [show Real.log v * (2 * (v - 2) / v) =
        2 * Real.log v / v * (v - 2) by ring]
    exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)
  intro a ha b hb hab
  have h := hanti (show 9 / 4 ≤ a ^ 2 + 9 / 4 by nlinarith [sq_nonneg a])
    (show 9 / 4 ≤ b ^ 2 + 9 / 4 by nlinarith [sq_nonneg b])
    (show a ^ 2 + 9 / 4 ≤ b ^ 2 + 9 / 4 by
      have hsq := pow_le_pow_left₀ ha hab 2
      linarith)
  convert h using 2 <;> ring

/-- P0014 page 35 after display 4.12, a left rectangle with a certified logarithm bound. -/
theorem log_sq_weight_cell (a b ℓ C : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hl : Real.log (a ^ 2 + 9 / 4) ≤ ℓ)
    (hC : (b - a) * ℓ ^ 2 / (1 / 4 + a ^ 2) ≤ C) :
    ∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ C := by
  let K := Real.log (a ^ 2 + 9 / 4) ^ 2 / (1 / 4 + a ^ 2)
  have hnorm : ‖∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)‖ ≤
      K * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro τ hτ
    rw [Set.uIoc_of_le hab] at hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact log_sq_weight_antitone ha (ha.trans hτ.1.le) hτ.1.le
  have hL0 : 0 ≤ Real.log (a ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg a])
  have hK : K ≤ ℓ ^ 2 / (1 / 4 + a ^ 2) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hL0 hl 2) (by positivity)
  calc (∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) ≤
      ‖∫ τ in a..b, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)‖ := by
        exact le_abs_self _
    _ ≤ K * (b - a) := by simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using hnorm
    _ ≤ (ℓ ^ 2 / (1 / 4 + a ^ 2)) * (b - a) :=
      mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hab)
    _ = (b - a) * ℓ ^ 2 / (1 / 4 + a ^ 2) := by ring
    _ ≤ C := hC

end LeanLab.HelfgottMajor.IntegralCells679

#print axioms LeanLab.HelfgottMajor.IntegralCells679.log_sq_weight_antitone

#print axioms LeanLab.HelfgottMajor.IntegralCells679.log_sq_weight_cell
