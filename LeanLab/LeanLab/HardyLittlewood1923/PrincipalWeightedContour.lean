import LeanLab.HardyLittlewood1923.InfiniteWeightedContour

/-!
AI wrote this Lean code for CODEX task52.
The principal residue in the exponential weighted contour is P0004 page 11 equation 2.416.
-/

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace LeanLab.HardyLittlewood1923.Task52

lemma weighted_rectangle_shift_principal {Θ : ℝ}
    (hZ : LeanLab.HardyLittlewood1923.U1473.NoZerosRightPrim Θ)
    {a T : ℝ} (hΘ : Θ < a) (ha : 1 / 2 ≤ a) (ha1 : a < 1) (hT : 0 < T)
    {z : ℂ} (hz : 0 < z.re) :
    VIntegral (weightedKernel (1 : DirichletCharacter ℂ 1) z) (3 / 2) (-T) T =
      VIntegral (weightedKernel (1 : DirichletCharacter ℂ 1) z) a (-T) T -
        HIntegral (weightedKernel (1 : DirichletCharacter ℂ 1) z) a (3 / 2) (-T) +
        HIntegral (weightedKernel (1 : DirichletCharacter ℂ 1) z) a (3 / 2) T +
        (2 * π * I) * z⁻¹ := by
  let K := weightedKernel (1 : DirichletCharacter ℂ 1) z
  let U := Rectangle ((a : ℂ) - I * T) ((3 / 2 : ℂ) + I * T)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hab : a ≤ 3 / 2 := by linarith
  have hre : ∀ s ∈ U, a ≤ s.re := by
    intro s hs
    have hs' := hs
    simp only [U, Rectangle, Complex.mem_reProdIm] at hs'
    have h := hs'.1
    simp only [sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
      sub_zero, add_re, one_mul, sub_self, add_zero] at h
    norm_num at h
    rw [Set.uIcc_of_le hab] at h
    exact h.1
  have hU : U ∈ 𝓝 (1 : ℂ) := by
    change Rectangle ((a : ℂ) - I * T) ((3 / 2 : ℂ) + I * T) ∈ 𝓝 (1 : ℂ)
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
      zero_mul, mul_zero, sub_zero, add_re, sub_self, add_zero, sub_im, mul_im,
      zero_sub, add_im, zero_add, one_re, one_im]
    norm_num
    constructor
    · simp only [Set.uIoo, min_eq_left hab, max_eq_right hab, mem_Ioo]
      exact ⟨ha1, by norm_num⟩
    · have ht : -T ≤ T := by linarith
      simp only [Set.uIoo, min_eq_left ht, max_eq_right ht, mem_Ioo]
      exact ⟨by linarith, hT⟩
  have hh : HolomorphicOn K (U \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hL := hZ 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one s (by linarith [hre s hs.1]) hs1
    exact (weightedKernel_differentiable_off_one _ hz0
      (by linarith [hre s hs.1]) hs1 hL).differentiableWithinAt
  let f : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s)
  let g : ℂ → ℂ := fun s => Complex.Gamma s * z ^ (-s)
  have hg : HolomorphicOn g U := by
    intro s hs
    have hsp : 0 < s.re := by linarith [hre s hs]
    have hG : DifferentiableAt ℂ Complex.Gamma s := by
      apply Complex.differentiableAt_Gamma
      intro n hn
      have he := congr_arg Complex.re hn
      simp at he
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hG.mul (DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inl hz0))).differentiableWithinAt
  have hf : (f - fun s : ℂ => (1 : ℂ) * (s - 1)⁻¹) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    have he : (f - fun s : ℂ => (1 : ℂ) * (s - 1)⁻¹) =
        (-deriv riemannZeta / riemannZeta - fun s : ℂ => (s - 1)⁻¹) := by
      funext s
      simp [f, neg_div]
    rw [he]
    exact riemannZetaLogDerivResidueBigO
  have hn := ResidueMult hg hU hf
  have hker : K = f * g := by
    funext s
    simp [K, weightedKernel, f, g, DirichletCharacter.LFunction_modOne_eq, mul_assoc]
  have hnear : (K - fun s : ℂ => z⁻¹ / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
    rw [hker]
    simpa only [g, Complex.Gamma_one, Complex.cpow_neg_one, one_mul, div_eq_mul_inv] using hn
  have hr : RectangleIntegral' K ((a : ℂ) - I * T) ((3 / 2 : ℂ) + I * T) = z⁻¹ := by
    apply ResidueTheoremOnRectangleWithSimplePole'
    · norm_num; linarith
    · simp; linarith
    · exact hU
    · exact hh
    · exact hnear
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero (by norm_num)
      exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  have hr' : RectangleIntegral K ((a : ℂ) - I * T) ((3 / 2 : ℂ) + I * T) =
      z⁻¹ * (2 * π * I) := by
    apply (div_eq_iff hpi).mp
    simpa only [RectangleIntegral', smul_eq_mul, div_eq_mul_inv, one_mul, mul_comm] using hr
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
    zero_mul, mul_zero, sub_zero, add_re, one_mul, sub_self, add_zero, sub_im, mul_im,
    add_im, zero_add, zero_sub] at hr'
  norm_num at hr'
  change VIntegral K (3 / 2) (-T) T = VIntegral K a (-T) T -
    HIntegral K a (3 / 2) (-T) + HIntegral K a (3 / 2) T + (2 * π * I) * z⁻¹
  linear_combination hr'

#print axioms weighted_rectangle_shift_principal

end LeanLab.HardyLittlewood1923.Task52
