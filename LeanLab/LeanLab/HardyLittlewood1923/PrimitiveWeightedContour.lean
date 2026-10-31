import LeanLab.HardyLittlewood1923.PrincipalWeightedContour

/-!
AI wrote this Lean code for CODEX task52.
This closes the complex exponential weighted contour identity for primitive characters.
Source P0004 page 11 equation 2.416, with the contour to the right of the zeros.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace LeanLab.HardyLittlewood1923.Task52

theorem weightedSum_shift_principal {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {σ : ℝ} (hΘ : Θ < σ) (h1 : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    {z : ℂ} (hz : 0 < z.re) :
    weightedSum (1 : DirichletCharacter ℂ 1) z = z⁻¹ + (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel (1 : DirichletCharacter ℂ 1) z ((σ : ℂ) + t * I)) := by
  let K := weightedKernel (1 : DirichletCharacter ℂ 1) z
  have hχ := DirichletCharacter.isPrimitive_one_level_one (R := ℂ)
  have h2 : σ ≤ 3 / 2 := by linarith
  have ha := weightedKernel_integrable hZ hχ hΘ h1 h2 (ne_of_lt hσ1) hz
  have hb := weightedKernel_integrable hZ hχ (lt_of_lt_of_le hΘ h2)
    (by norm_num : (1 : ℝ) / 2 ≤ 3 / 2) (by norm_num : (3 : ℝ) / 2 ≤ 3 / 2)
    (by norm_num : (3 : ℝ) / 2 ≠ 1) hz
  obtain ⟨hlo, hhi⟩ := weighted_horizontal_decay hZ hχ h2 h1
    (by norm_num : (3 : ℝ) / 2 ≤ 3 / 2) hΘ hz
  have hla := (intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id).const_smul
    (I : ℂ)
  have hlb := (intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id).const_smul
    (I : ℂ)
  let R : ℂ := (2 * π * I) * z⁻¹
  have ht : Tendsto (fun T : ℝ => VIntegral K σ (-T) T - HIntegral K σ (3 / 2) (-T) +
      HIntegral K σ (3 / 2) T + R) atTop
      (𝓝 (I • (∫ t : ℝ, K ((σ : ℂ) + t * I)) + R)) := by
    simpa only [K, VIntegral, sub_zero, add_zero, id_eq] using
      (((hla.sub hlo).add hhi).add_const R)
  have he : ∀ᶠ T : ℝ in atTop, VIntegral K (3 / 2) (-T) T =
      VIntegral K σ (-T) T - HIntegral K σ (3 / 2) (-T) + HIntegral K σ (3 / 2) T + R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact weighted_rectangle_shift_principal hZ hΘ h1 hσ1 hT hz
  have ht' : Tendsto (fun T : ℝ => VIntegral K (3 / 2) (-T) T) atTop
      (𝓝 (I • (∫ t : ℝ, K ((σ : ℂ) + t * I)) + R)) := (tendsto_congr' he).mpr ht
  simp only [K, VIntegral, id_eq] at ht'
  simp only [id_eq] at hlb
  have hu := tendsto_nhds_unique hlb ht'
  simp only [smul_eq_mul] at hu
  have hi : (∫ t : ℝ, K ((((3 / 2 : ℝ) : ℂ)) + t * I)) =
      (∫ t : ℝ, K ((σ : ℂ) + t * I)) + (2 * π) * z⁻¹ := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc _ = I * (∫ t : ℝ, K ((σ : ℂ) + t * I)) + R := hu
      _ = _ := by dsimp [R]; ring
  rw [weightedSum_mellin_right (1 : DirichletCharacter ℂ 1) (σ := 3 / 2)
    (by norm_num) (by norm_num) hz]
  change (1 / (2 * (π : ℂ))) * (∫ t : ℝ, K ((((3 / 2 : ℝ) : ℂ)) + t * I)) =
    z⁻¹ + (1 / (2 * (π : ℂ))) * (∫ t : ℝ, K ((σ : ℂ) + t * I))
  rw [hi]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ t : ℝ, K ((σ : ℂ) + t * I)) = J
  field_simp [hpi] <;> ring

/-- The weighted contour identity for every primitive character, including its principal term. -/
theorem weightedSum_shift_primitive {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {σ : ℝ} (hΘ : Θ < σ) (h1 : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    {z : ℂ} (hz : 0 < z.re) :
    weightedSum χ z - (if q = 1 then z⁻¹ else 0) = (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel χ z ((σ : ℂ) + t * I)) := by
  by_cases hq : q = 1
  · subst q
    have hc : χ = 1 := by
      ext n
      have hn : (n : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [hn]
      simp
    rw [hc, if_pos rfl, weightedSum_shift_principal hZ hΘ h1 hσ1 hz]
    ring
  · rw [if_neg hq, sub_zero]
    exact weightedSum_shift_nonprincipal hZ hχ hq hΘ h1 (by linarith) (ne_of_lt hσ1) hz

/-- The weighted contour lemma on the requested lower range of Theta. -/
theorem weightedSum_shift_lower_all {Θ : ℝ} (h0 : 1 / 2 ≤ Θ) (_hΘ : Θ < 47 / 64)
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1 - Θ) {z : ℂ} (hz : 0 < z.re) :
    weightedSum χ z - (if q = 1 then z⁻¹ else 0) = (1 / (2 * (π : ℂ))) *
      (∫ t : ℝ, weightedKernel χ z (((Θ + η : ℝ) : ℂ) + t * I)) := by
  exact weightedSum_shift_primitive hZ hχ (by linarith) (by linarith) (by linarith) hz

#print axioms weightedSum_shift_principal
#print axioms weightedSum_shift_primitive
#print axioms weightedSum_shift_lower_all

end LeanLab.HardyLittlewood1923.Task52
