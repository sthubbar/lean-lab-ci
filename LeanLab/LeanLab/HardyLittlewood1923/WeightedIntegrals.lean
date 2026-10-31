import LeanLab.HardyLittlewood1923.WeightedBounds

/-!
AI wrote this Lean code for CODEX task52.
These line integrability lemmas justify the weighted contour in P0004 page 11.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open LeanLab.HardyLittlewood1923.U1503 (KW lZ KW_pos lZ_pos)
open LeanLab.PNTPort.DirichletZF (Z Z_pos)

namespace LeanLab.HardyLittlewood1923.Task52

lemma weightedKernel_differentiable_off_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z s : ℂ} (hz : z ≠ 0) (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (weightedKernel χ z) s := by
  have hLA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {w : ℂ | w ≠ 1} :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt)
      isOpen_ne
  have hD := (hLA s hs1).deriv.differentiableAt
  have hG : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have h := congr_arg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (((hD.div (hLA s hs1).differentiableAt hL).neg).mul hG).mul
    (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hz))

lemma weightedKernel_line_envelope {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) (hσ1 : σ ≠ 1)
    {z : ℂ} (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ ≤
      C * (1 + |t|) ^ 3 * Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
  obtain ⟨G, hG, hg⟩ := gamma_kernel_uniform hz
  let η := σ - Θ
  have hη : 0 < η := sub_pos.mpr hσ
  let A := (KW + 1 / (lZ * η)) * (960 * q * Z)
  have hK := KW_pos
  have hl := lZ_pos
  have hZp := Z_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have habs : 0 < |σ - 1| := abs_pos.mpr (sub_ne_zero.mpr hσ1)
  let D := A + |σ - 1|⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * G, mul_pos hD hG, fun t => ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    apply hσ1
    have he := congr_arg Complex.re h
    simpa using he
  have hb := logDeriv_polynomial_bound hZ hχ hη (by dsimp [η]; linarith) h1 h2 hs1
  have hpole : ‖(σ : ℂ) + t * I - 1‖⁻¹ ≤ |σ - 1|⁻¹ := by
    apply inv_anti₀ habs
    simpa using Complex.abs_re_le_norm ((σ : ℂ) + t * I - 1)
  have hsq : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_nonneg |t|]
  have hB : ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ D * (1 + |t|) ^ 2 := by
    calc _ ≤ A * (1 + |t|) ^ 2 + ‖(σ : ℂ) + t * I - 1‖⁻¹ := hb
      _ ≤ A * (1 + |t|) ^ 2 + |σ - 1|⁻¹ := by linarith only [hpole]
      _ ≤ D * (1 + |t|) ^ 2 := by
        dsimp [D]
        nlinarith only [mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (abs_nonneg (σ - 1)))]
  have he : ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ =
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ *
        ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ := by
    simp [weightedKernel, norm_mul, mul_assoc]
  rw [he]
  calc _ ≤ (D * (1 + |t|) ^ 2) *
        (G * (1 + |t|) * Real.exp (-((π / 2 - |Complex.arg z|) * |t|))) :=
      mul_le_mul hB (hg σ h1 h2 t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma weightedKernel_integrable {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 3 / 2) (hσ1 : σ ≠ 1)
    {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ => weightedKernel χ z ((σ : ℂ) + t * I)) := by
  obtain ⟨C, hC, hc⟩ := weightedKernel_line_envelope hZ hχ hσ h1 h2 hσ1 hz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hcont : Continuous (fun t : ℝ => weightedKernel χ z ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs1 : (σ : ℂ) + t * I ≠ 1 := by
      intro h
      apply hσ1
      have he := congr_arg Complex.re h
      simpa using he
    have hL := hZ q χ hχ ((σ : ℂ) + t * I) (by simpa using hσ) hs1
    have hd := weightedKernel_differentiable_off_one χ hz0
      (by simpa using (show (0 : ℝ) < σ by linarith)) hs1 hL
    exact hd.continuousAt.comp (f := fun u : ℝ => (σ : ℂ) + u * I) (by fun_prop)
  refine Integrable.mono' ((integrable_polynomial_exp_abs 3 (kernel_decay_pos hz)).const_mul C)
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  simpa only [mul_assoc, neg_mul] using hc t

#print axioms weightedKernel_differentiable_off_one
#print axioms weightedKernel_line_envelope
#print axioms weightedKernel_integrable

end LeanLab.HardyLittlewood1923.Task52
