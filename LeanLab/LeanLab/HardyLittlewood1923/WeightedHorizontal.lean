import LeanLab.HardyLittlewood1923.WeightedIntegrals

/-!
AI wrote this Lean code for CODEX task52.
The horizontal edge estimates justify the exponential weighted shift after P0004 equation 2.416.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology
open LeanLab.HardyLittlewood1923.U1503 (KW lZ KW_pos lZ_pos)
open LeanLab.PNTPort.DirichletZF (Z Z_pos)

namespace LeanLab.HardyLittlewood1923.Task52

lemma weightedKernel_horizontal_envelope {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {a b : ℝ} (h1 : 1 / 2 ≤ a) (h2 : b ≤ 3 / 2) (hΘ : Θ < a)
    {z : ℂ} (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ |t| →
      ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ ≤
        C * (1 + |t|) ^ 3 * Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
  obtain ⟨G, hG, hg⟩ := gamma_kernel_uniform hz
  let η := a - Θ
  have hη : 0 < η := sub_pos.mpr hΘ
  let A := (KW + 1 / (lZ * η)) * (960 * q * Z)
  have hK := KW_pos
  have hl := lZ_pos
  have hZp := Z_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(A + 1) * G, by positivity, fun σ ha hb t ht => ?_⟩
  have hs1 : (σ : ℂ) + t * I ≠ 1 := by
    intro h
    have he := congr_arg Complex.im h
    simp at he
    norm_num [he] at ht
  have hpole : ‖(σ : ℂ) + t * I - 1‖⁻¹ ≤ 1 := by
    have hn : 1 ≤ ‖(σ : ℂ) + t * I - 1‖ := by
      have hh := Complex.abs_im_le_norm ((σ : ℂ) + t * I - 1)
      have hh' : |t| ≤ ‖(σ : ℂ) + t * I - 1‖ := by simpa using hh
      exact ht.trans hh'
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hn
  have hsσ : Θ + η ≤ σ := by dsimp [η]; linarith
  have hσ1 : 1 / 2 ≤ σ := h1.trans ha
  have hσ2 : σ ≤ 3 / 2 := hb.trans h2
  have hd := logDeriv_polynomial_bound hZ hχ hη hsσ hσ1 hσ2 hs1
  have hsq : 1 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_nonneg |t|]
  have hD : ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ ≤ (A + 1) * (1 + |t|) ^ 2 := by
    change _ ≤ A * (1 + |t|) ^ 2 + ‖(σ : ℂ) + t * I - 1‖⁻¹ at hd
    nlinarith only [hd, hpole, hsq]
  have he : ‖weightedKernel χ z ((σ : ℂ) + t * I)‖ =
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)‖ *
        ‖Complex.Gamma ((σ : ℂ) + t * I) * z ^ (-((σ : ℂ) + t * I))‖ := by
    simp [weightedKernel, norm_mul, mul_assoc]
  rw [he]
  calc _ ≤ ((A + 1) * (1 + |t|) ^ 2) *
        (G * (1 + |t|) * Real.exp (-((π / 2 - |Complex.arg z|) * |t|))) :=
      mul_le_mul hD (hg σ hσ1 hσ2 t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma weighted_horizontal_decay {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {a b : ℝ} (hab : a ≤ b) (h1 : 1 / 2 ≤ a) (h2 : b ≤ 3 / 2) (hΘ : Θ < a)
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun T : ℝ => HIntegral (weightedKernel χ z) a b (-T)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral (weightedKernel χ z) a b T) atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := weightedKernel_horizontal_envelope hZ hχ h1 h2 hΘ hz
  let B := C * (b - a)
  have hnorm : ∀ t : ℝ, 1 ≤ |t| → ‖HIntegral (weightedKernel χ z) a b t‖ ≤
      B * (1 + |t|) ^ 3 * Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) := by
    intro t ht
    have h := U1503.horiz_le hab (le_refl (b - a))
      (show 0 ≤ C * (1 + |t|) ^ 3 * Real.exp (-((π / 2 - |Complex.arg z|) * |t|)) by positivity)
      (fun σ ha hb => hc σ ha hb t ht)
    change ‖HIntegral (weightedKernel χ z) a b t‖ ≤ _ at h
    calc _ ≤ _ := h
      _ = _ := by dsimp [B]; ring
  have hl : Tendsto (fun T : ℝ => B * (1 + T) ^ 3 *
      Real.exp (-((π / 2 - |Complex.arg z|) * T))) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc, neg_mul] using
      (polynomial_exp_tendsto_zero 3 (kernel_decay_pos hz)).const_mul B
  constructor
  · apply squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have h := hnorm (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT)
    simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using h
  · apply squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have h := hnorm T (by rw [abs_of_nonneg (by linarith)]; exact hT)
    simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using h

#print axioms weightedKernel_horizontal_envelope
#print axioms weighted_horizontal_decay

end LeanLab.HardyLittlewood1923.Task52
