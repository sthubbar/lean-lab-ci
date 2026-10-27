import LeanLab.HardyLittlewood1923.GammaMoment

/-!
AI wrote this Lean code for CODEX task52.
P0004 page 11 weighted contour and page 19 Gamma decay.
The bound has an explicit epsilon loss and is not the full printed error bound.
-/

open Complex Real Set MeasureTheory

namespace LeanLab.HardyLittlewood1923.Task52

lemma weightedKernel_sharp_envelope {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ ε : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 < z.re → ∀ t : ℝ,
      ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ ≤
        C * ‖z‖ ^ (-σ) * (1 + |t|) ^ (σ - 1 / 2 + ε) *
          Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
  obtain ⟨D, hD, hd⟩ := logDeriv_small_power hZ hχ hσ h1 (by linarith) (by linarith) hε
  let G := Real.sqrt (2 * π) * Real.exp (5 / 2)
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨D * G * (5 / 2), by positivity, fun z hz t => ?_⟩
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hg := gamma_kernel_bound (s := (σ : ℂ) + t * I)
    (by simpa using h1) (by simpa using (show σ ≤ 3 / 2 by linarith)) hz0
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_self, add_zero, add_im, zero_add, mul_im, mul_one] at hg
  have hn := norm_line_add_one_sharp h1 (by linarith) t
  have hgg : ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ ≤
      G * ‖z‖ ^ (-σ) * ((5 / 2) * (1 + |t|) ^ (σ - 1 / 2)) *
        Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
    calc _ ≤ _ := hg
      _ ≤ _ := by gcongr
  have he : ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ =
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ *
        ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ := by
    simp [weightedKernel, mul_assoc]
  rw [he]
  calc _ ≤ (D * (1 + |t|) ^ ε) *
      (G * ‖z‖ ^ (-σ) * ((5 / 2) * (1 + |t|) ^ (σ - 1 / 2)) *
        Real.exp (-((π / 2 - |Complex.arg z|) * |t|))) :=
      mul_le_mul (hd t) hgg (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.rpow_add (by linarith [abs_nonneg t] : 0 < 1 + |t|)]
      ring

lemma weightedSum_error_bound {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ ε : ℝ} (hσ : Θ < σ) (h1 : 1 / 2 ≤ σ) (h2 : σ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 < z.re →
      let δ := π / 2 - |Complex.arg z|
      ‖weightedSum χ z - (if q = 1 then z⁻¹ else 0)‖ ≤ C * ‖z‖ ^ (-σ) *
        (1 / δ + (1 / δ) ^ (σ + 1 / 2 + ε) * Real.Gamma (σ + 1 / 2 + ε)) := by
  obtain ⟨D, hD, hd⟩ := weightedKernel_sharp_envelope hZ hχ hσ h1 h2 hε
  refine ⟨D * 8 / (2 * π), by positivity, fun z hz => ?_⟩
  dsimp only
  let δ := π / 2 - |Complex.arg z|
  let p := σ - 1 / 2 + ε
  have hδ : 0 < δ := kernel_decay_pos hz
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hp2 : p ≤ 2 := by dsimp [p]; linarith
  have hf := weightedKernel_integrable hZ hχ hσ h1 (by linarith) (by linarith) hz
  have he := integrable_rpow_envelope hp hp2 hδ
  have hm : (∫ t : ℝ, ‖weightedKernel χ z ((σ : ℂ) + t * I)‖) ≤
      D * ‖z‖ ^ (-σ) * (∫ t : ℝ, (1 + |t|) ^ p * Real.exp (-(δ * |t|))) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hf.norm (he.const_mul _)
    filter_upwards [] with t
    simpa only [p, δ, mul_assoc] using hd z hz t
  rw [weightedSum_shift_primitive hZ hχ hσ h1 h2 hz, norm_mul]
  have hc : ‖(1 : ℂ) / (2 * (π : ℂ))‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hc]
  have hi := integral_rpow_envelope_le hp hp2 hδ
  have hpp : p + 1 = σ + 1 / 2 + ε := by dsimp [p]; ring
  rw [hpp] at hi
  calc _ ≤ (1 / (2 * π)) * (∫ t : ℝ, ‖weightedKernel χ z ((σ : ℂ) + t * I)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (1 / (2 * π)) * (D * ‖z‖ ^ (-σ) *
        (8 * (1 / δ + (1 / δ) ^ (σ + 1 / 2 + ε) * Real.Gamma (σ + 1 / 2 + ε)))) := by
      exact mul_le_mul_of_nonneg_left
        (hm.trans (mul_le_mul_of_nonneg_left hi (by positivity))) (by positivity)
    _ = _ := by ring

#print axioms weightedKernel_sharp_envelope
#print axioms weightedSum_error_bound

end LeanLab.HardyLittlewood1923.Task52
