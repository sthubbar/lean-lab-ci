/-
PROVED leaf `leaf_y1_dominates` of SPLIT_Decomp409b, P0069 page 24: y1 x = x exp(-3 L^(1/3))
exceeds x^0.96 L^A for large x. The statement is restated verbatim as
`leaf_y1_dominates_proof`. Route: in u = log x, 3 u^(1/3) + A log u is at most 0.04 u
eventually, then exponentiate. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_Decomp409b

noncomputable section
open Filter Asymptotics
namespace LeanLab.BakerHarmanPintz1997.Decomp409b

/-- `leaf_y1_dominates`, verbatim, proved. -/
theorem leaf_y1_dominates_proof (A : ℝ) (hA : 0 < A) :
    ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x → x ^ (0.96 : ℝ) ≤ y1 x / L x ^ A := by
  -- eventual inequality in u = log x
  have h1 : ∀ᶠ u : ℝ in atTop, 150 ≤ u ^ (2/3 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 2/3)).eventually_ge_atTop 150
  have h2 : ∀ᶠ u : ℝ in atTop, ‖Real.log u‖ ≤ (0.02 / A) * ‖id u‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  have h3 : ∀ᶠ u : ℝ in atTop, 1 ≤ u := eventually_ge_atTop 1
  have hu : ∀ᶠ u : ℝ in atTop, 3 * u ^ (1/3 : ℝ) + A * Real.log u ≤ 0.04 * u := by
    filter_upwards [h1, h2, h3] with u hu1 hu2 hu3
    have hu0 : 0 < u := by linarith
    have hsplit : u = u ^ (1/3 : ℝ) * u ^ (2/3 : ℝ) := by
      rw [← Real.rpow_add hu0]; norm_num
    have hp : 0 ≤ u ^ (1/3 : ℝ) := Real.rpow_nonneg hu0.le _
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu3
    rw [Real.norm_eq_abs, abs_of_nonneg hlog, id, Real.norm_eq_abs, abs_of_pos hu0] at hu2
    have e1 : 150 * u ^ (1/3 : ℝ) ≤ u := by
      calc 150 * u ^ (1/3 : ℝ) ≤ u ^ (2/3 : ℝ) * u ^ (1/3 : ℝ) :=
            mul_le_mul_of_nonneg_right hu1 hp
        _ = u := by rw [mul_comm]; exact hsplit.symm
    have e2 : A * Real.log u ≤ 0.02 * u := by
      have := mul_le_mul_of_nonneg_left hu2 hA.le
      calc A * Real.log u ≤ A * (0.02 / A * u) := this
        _ = 0.02 * u := by field_simp
    linarith
  obtain ⟨U, hU⟩ := eventually_atTop.1 (Real.tendsto_log_atTop.eventually hu)
  refine ⟨max U 3, fun x hx => ?_⟩
  have hx3 : (3:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hk := hU x (le_trans (le_max_left _ _) hx)
  have hL : 0 < L x := Real.log_pos (by linarith)
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos hL _
  rw [le_div_iff₀ hLA]
  have ex1 : x ^ (0.96 : ℝ) = Real.exp (Real.log x * 0.96) := Real.rpow_def_of_pos hx0 _
  have ex2 : L x ^ A = Real.exp (Real.log (Real.log x) * A) := by
    unfold L; exact Real.rpow_def_of_pos hL _
  have ex3 : y1 x = Real.exp (Real.log x + -3 * Real.log x ^ (1 / 3 : ℝ)) := by
    unfold y1; rw [Real.exp_add, Real.exp_log hx0]
  rw [ex1, ex2, ex3, ← Real.exp_add, Real.exp_le_exp]
  nlinarith

#print axioms leaf_y1_dominates_proof

end LeanLab.BakerHarmanPintz1997.Decomp409b
