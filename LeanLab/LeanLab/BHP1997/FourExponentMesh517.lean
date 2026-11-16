/-
P0069, Section 5, page 51, display 5.17 reached from display 5.15 on page 50.
Elementary estimates for the exponent cells of the E4 integral.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace LeanLab.BHP1997.LowerShortC165
open Filter Real

/-- Page 51 display 5.17. The four mesh weights factor exactly. -/
theorem four_exponent_mesh_product (L a b c d : ℝ) :
    (1 / (a * L) * (1 / (b * L)) * (1 / (c * L)) * (1 / (d * L))) =
      (1 / L) ^ 4 * (1 / (a * b * c * d)) := by
  simp only [one_div, mul_inv_rev]
  ring

/-- Page 51 display 5.17. A logarithmic cell has width between its two endpoint weights. -/
theorem four_exponent_mesh_bounds {Z n : ℝ} (hZ : 1 < Z) (hn : 0 < n) :
    1 / ((n + 1) * Real.log Z) ≤
        Real.log (n + 1) / Real.log Z - Real.log n / Real.log Z ∧
      Real.log (n + 1) / Real.log Z - Real.log n / Real.log Z ≤
        1 / (n * Real.log Z) := by
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hn1 : 0 < n + 1 := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn)
  have hhi := Real.log_le_sub_one_of_pos (div_pos hn1 hn)
  rw [Real.log_div hn1.ne' hn.ne'] at hlo hhi
  have el : 1 - ((n + 1) / n)⁻¹ = 1 / (n + 1) := by field_simp; ring
  have eu : (n + 1) / n - 1 = 1 / n := by field_simp; ring
  rw [el] at hlo
  rw [eu] at hhi
  rw [← sub_div, ← div_div, ← div_div]
  exact ⟨div_le_div_of_nonneg_right hlo hL.le,
    div_le_div_of_nonneg_right hhi hL.le⟩

/-- Page 51 display 5.17. Replacing the exact cell width by its mesh weight costs at most
one over n squared log Z. -/
theorem four_exponent_mesh_error {Z n : ℝ} (hZ : 1 < Z) (hn : 0 < n) :
    0 ≤ 1 / (n * Real.log Z) -
        (Real.log (n + 1) / Real.log Z - Real.log n / Real.log Z) ∧
      1 / (n * Real.log Z) -
        (Real.log (n + 1) / Real.log Z - Real.log n / Real.log Z) ≤
        1 / (n ^ 2 * Real.log Z) := by
  obtain ⟨hlo, hhi⟩ := four_exponent_mesh_bounds hZ hn
  refine ⟨sub_nonneg.mpr hhi, ?_⟩
  have hL : 0 < Real.log Z := Real.log_pos hZ
  calc _ ≤ 1 / (n * Real.log Z) - 1 / ((n + 1) * Real.log Z) := by linarith
    _ = 1 / (n * (n + 1) * Real.log Z) := by field_simp; ring
    _ ≤ 1 / (n ^ 2 * Real.log Z) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith

/-- Page 51 display 5.17. An exponent at least one tenth gives an integer
index at least Z to the power one tenth. -/
theorem four_exponent_index_lower {Z : ℝ} (hZ : 1 < Z) {n : ℕ}
    (hn : (1/10 : ℝ) ≤ Real.log (n : ℝ) / Real.log Z) :
    Z ^ (1/10 : ℝ) ≤ (n : ℝ) := by
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [Real.rpow_le_iff_le_log (by linarith : 0 < Z) hnp]
  exact (le_div_iff₀ hL).mp hn

/-- Page 51 display 5.17. Above the index cutoff the exponent mesh saves a
power of Z. -/
theorem four_exponent_mesh_power_bound {Z n : ℝ} (hZ : 1 < Z)
    (hn : Z ^ (1/10 : ℝ) ≤ n) :
    Real.log (n + 1) / Real.log Z - Real.log n / Real.log Z ≤
      Z ^ (-(1/10) : ℝ) / Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hnp : 0 < n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
  have hL : 0 < Real.log Z := Real.log_pos hZ
  calc _ ≤ 1 / (n * Real.log Z) := (four_exponent_mesh_bounds hZ hnp).2
    _ ≤ 1 / (Z ^ (1/10 : ℝ) * Real.log Z) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hn hL.le)
    _ = Z ^ (-(1/10) : ℝ) / Real.log Z := by
      rw [Real.rpow_neg hZ0.le]
      simp only [one_div, mul_inv_rev, div_eq_mul_inv]
      ring

/-- Page 51 display 5.17. Any fixed power saving absorbs every power of log x. -/
theorem four_exponent_power_absorbs_log (A δ K : ℝ) (hδ : 0 < δ) :
    ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      K * x ^ (-δ) ≤ Real.log x ^ (-A) := by
  have h := (isLittleO_log_rpow_rpow_atTop A hδ).bound
    (show (0 : ℝ) < 1 / (|K| + 1) by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp h
  refine ⟨max X 2, le_max_right _ _, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := (le_max_right X 2).trans hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hLp : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL _
  have hxp : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 _
  have hb := hX x ((le_max_left X 2).trans hx)
  rw [Real.norm_of_nonneg hLp.le, Real.norm_of_nonneg hxp.le] at hb
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hL.le]
  rw [← one_div (Real.log x ^ A), le_div_iff₀ hLp]
  have hb' : (|K| + 1) * Real.log x ^ A ≤ x ^ δ := by
    calc _ ≤ (|K| + 1) * (1 / (|K| + 1) * x ^ δ) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = x ^ δ := by field_simp
  have hK : K * Real.log x ^ A ≤ x ^ δ := by
    calc _ ≤ (|K| + 1) * Real.log x ^ A := by
          gcongr
          exact (le_abs_self K).trans (by linarith [abs_nonneg K])
      _ ≤ _ := hb'
  calc K * (x ^ δ)⁻¹ * Real.log x ^ A =
      (K * Real.log x ^ A) / x ^ δ := by ring
    _ ≤ 1 := (div_le_one hxp).mpr hK

#print axioms four_exponent_mesh_product
#print axioms four_exponent_mesh_bounds
#print axioms four_exponent_mesh_error
#print axioms four_exponent_index_lower
#print axioms four_exponent_mesh_power_bound
#print axioms four_exponent_power_absorbs_log
end LeanLab.BHP1997.LowerShortC165
