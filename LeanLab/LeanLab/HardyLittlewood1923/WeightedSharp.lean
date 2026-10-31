import LeanLab.HardyLittlewood1923.PrimitiveWeightedContour

/-!
AI wrote this Lean code for CODEX task52.
P0004 pages 11 and 19, quantitative weighted contour estimates.
The small power epsilon retains the sharp Gamma polynomial exponent.
-/

open Complex Real Set MeasureTheory
open LeanLab.HardyLittlewood1923.U1503 (KW lZ KW_pos lZ_pos logDeriv_region)
open LeanLab.PNTPort.DirichletZF (Z Z_pos)

namespace LeanLab.HardyLittlewood1923.Task52

lemma log_height_power {A ε t : ℝ} (hA : 0 < A) (hε : 0 < ε) (ht : 0 ≤ t) :
    Real.log (A * (1 + t) ^ 2) ≤ (|Real.log A| + 2 / ε) * (1 + t) ^ ε := by
  have hp : 1 ≤ (1 + t) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hl := Real.log_le_rpow_div (by linarith : 0 ≤ 1 + t) hε
  rw [Real.log_mul hA.ne' (by positivity), Real.log_pow]
  have ha : Real.log A ≤ |Real.log A| * (1 + t) ^ ε :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hp)
  calc _ ≤ |Real.log A| * (1 + t) ^ ε + 2 * ((1 + t) ^ ε / ε) :=
      add_le_add ha (mul_le_mul_of_nonneg_left hl (by norm_num))
    _ = _ := by ring

lemma logDeriv_small_power {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ ε : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2)
    (hσ1 : σ ≠ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ ε := by
  let η := σ - Θ
  have hη : 0 < η := sub_pos.mpr hσ
  have hK := KW_pos
  have hl := lZ_pos
  have hz := Z_pos
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let A := 960 * (q : ℝ) * Z
  let B := KW + 1 / (lZ * η)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have ha : 0 < |σ - 1| := abs_pos.mpr (sub_ne_zero.mpr hσ1)
  refine ⟨B * (|Real.log A| + 2 / ε) + |σ - 1|⁻¹, by positivity, fun t => ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    apply hσ1
    simpa using congr_arg Complex.re h
  have hd := logDeriv_region hZ hχ hη (by dsimp [η]; linarith) h1 (by linarith) hs1
  have hp : ‖(σ : ℂ) + t * I - 1‖⁻¹ ≤ |σ - 1|⁻¹ := by
    apply inv_anti₀ ha
    simpa using Complex.abs_re_le_norm ((σ : ℂ) + t * I - 1)
  have hs : (|t| + 4) ^ 2 ≤ 16 * (1 + |t|) ^ 2 := by
    nlinarith [abs_nonneg t, sq_nonneg |t|]
  have hm : 60 * q * (|t| + 4) ^ 2 * Z ≤ A * (1 + |t|) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 60 * q * Z by positivity)
    dsimp [A]
    nlinarith only [h]
  have hlog : Real.log (60 * q * (|t| + 4) ^ 2 * Z) ≤
      (|Real.log A| + 2 / ε) * (1 + |t|) ^ ε :=
    (Real.log_le_log (by positivity) hm).trans (log_height_power hA hε (abs_nonneg t))
  have hp1 : 1 ≤ (1 + |t|) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg t]) hε.le
  calc _ ≤ B * Real.log (60 * q * (|t| + 4) ^ 2 * Z) +
      ‖(σ : ℂ) + t * I - 1‖⁻¹ := hd
    _ ≤ B * ((|Real.log A| + 2 / ε) * (1 + |t|) ^ ε) + |σ - 1|⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB.le) hp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hp1 (inv_nonneg.mpr (abs_nonneg (σ - 1)))
      nlinarith only [hh]

lemma norm_line_add_one_sharp {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) (t : ℝ) :
    ‖((σ : ℂ) + t * I) + 1‖ ^ (σ - 1 / 2) ≤ (5 / 2) * (1 + |t|) ^ (σ - 1 / 2) := by
  have ha : 0 ≤ σ - 1 / 2 := by linarith
  have hnorm : ‖((σ : ℂ) + t * I) + 1‖ ≤ (5 / 2) * (1 + |t|) := by
    have he : ((σ : ℂ) + t * I) + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [he]
    calc _ ≤ ‖((σ + 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = σ + 1 + |t| := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ σ + 1),
          norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [abs_nonneg t]
  calc _ ≤ ((5 / 2) * (1 + |t|)) ^ (σ - 1 / 2) := Real.rpow_le_rpow (norm_nonneg _) hnorm ha
    _ = (5 / 2 : ℝ) ^ (σ - 1 / 2) * (1 + |t|) ^ (σ - 1 / 2) :=
      Real.mul_rpow (by norm_num) (by linarith [abs_nonneg t])
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc (5 / 2 : ℝ) ^ (σ - 1 / 2) ≤ (5 / 2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by rw [Real.rpow_one]

#print axioms log_height_power
#print axioms logDeriv_small_power
#print axioms norm_line_add_one_sharp

end LeanLab.HardyLittlewood1923.Task52
