import LeanLab.HelfgottMajor.Mellin389

/-!
Differentiation and the logarithm weighted Gaussian profile on book page 434.
Source P0014 page 43 display 4.42 and book page 433 display 16.24.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MellinDerivative431
open Real MeasureTheory Filter Asymptotics Set LeanLab.HelfgottArcs Decomp269a Mellin389
open scoped Topology FourierTransform

/-- The Mellin derivative profile after the substitution t equal to exp of minus u.
Source book page 434, differentiated Plancherel display.
-/
noncomputable def logWeightedGaussian (δ u : ℝ) : ℂ := (-u) • logGaussian δ u

/-- The Gaussian Mellin transform has the log weighted Mellin derivative in the strip.
Source book page 433 display 16.24 and page 434.
-/
theorem gaussian_mellin_hasDerivAt (δ : ℝ) (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) s ∧
      HasDerivAt (gaussianMellin δ)
        (mellin (fun t : ℝ => log t • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) s) s := by
  let f : ℝ → ℂ := fun t => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)
  have hn (t : ℝ) : ‖f t‖ = exp (-t ^ 2 / 2) := by
    have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    have he := he0 (δ * t)
    dsimp only [f]
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  have hc : Continuous f := by unfold f e; fun_prop
  have htop : f =O[atTop] (fun t : ℝ => t ^ (-(1 : ℝ))) := by
    rw [← isBigO_norm_left]
    simp_rw [hn]
    have hexp : (fun t : ℝ => exp (-t)) =O[atTop] (fun t : ℝ => t ^ (-1 : ℝ)) := by
      simpa only [one_mul, neg_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1) (-1)).isBigO
    have hh := (exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2)).isBigO.trans hexp
    simpa only [one_mul, neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using hh
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
    apply isBigO_iff.mpr
    refine ⟨1, Eventually.of_forall fun t => ?_⟩
    simp only [hn, neg_zero, rpow_zero, norm_one, mul_one]
    exact exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  exact mellin_hasDerivAt_of_isBigO_rpow
    (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi) htop hs1 hbot hs

/-- The Mellin derivative on the critical line is the Fourier transform of the weighted profile.
Source book page 434, the sentence before differentiated Plancherel.
-/
theorem derivative_eq_fourier (δ τ : ℝ) :
    deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) =
      𝓕 (logWeightedGaussian δ) (τ / (2 * π)) := by
  rw [(gaussian_mellin_hasDerivAt δ _ (by norm_num) (by norm_num)).2.deriv,
    mellin_eq_fourier]
  have hr : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).re = (1 / 2 : ℝ) := by norm_num
  have hi : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).im = τ := by norm_num
  rw [hr, hi]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (τ / (2 * π)))
  funext u
  simp only [log_exp, logWeightedGaussian, logGaussian]
  rw [smul_comm]
  congr 1
  congr 1
  congr 1
  ring

/-- The weighted logarithmic input squared norm is the log squared Gaussian density.
Source book page 434 and P0014 page 43 display 4.42.
-/
theorem logWeightedGaussian_norm_sq (δ u : ℝ) :
    ‖logWeightedGaussian δ u‖ ^ 2 = u ^ 2 * exp (-u) * exp (-(exp (-u)) ^ 2) := by
  rw [logWeightedGaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    neg_sq, logGaussian_norm_sq]
  ring

/-- The weighted logarithmic profile is square integrable.
Source book page 434, differentiated Plancherel prerequisite.
-/
theorem logWeightedGaussian_memLp_two (δ : ℝ) : MemLp (logWeightedGaussian δ) 2 := by
  have hi := (integrable_comp_exp (fun t : ℝ => exp (-t ^ 2) * log t ^ 2)).mpr
    gaussian_log_square_integrable
  have hn := hi.comp_neg
  apply (memLp_two_iff_integrable_sq_norm (by unfold logWeightedGaussian logGaussian e; fun_prop)).mpr
  apply hn.congr
  filter_upwards [] with u
  simp only [smul_eq_mul, log_exp, logWeightedGaussian_norm_sq, neg_sq]
  ring

/-- The weighted profile input energy equals the actual log squared Gaussian moment.
Source book page 434 and P0014 page 43 display 4.42.
-/
theorem logWeightedGaussian_square_integral (δ : ℝ) :
    (∫ u : ℝ, ‖logWeightedGaussian δ u‖ ^ 2) =
      ∫ t in Ioi (0 : ℝ), exp (-t ^ 2) * log t ^ 2 := by
  simp_rw [logWeightedGaussian_norm_sq]
  have hneg := integral_neg_eq_self (fun u : ℝ => u ^ 2 * exp u * exp (-(exp u) ^ 2))
  simp only [neg_sq] at hneg
  rw [hneg]
  have heq : (fun u : ℝ => u ^ 2 * exp u * exp (-(exp u) ^ 2)) =
      (fun u : ℝ => exp u • (exp (-(exp u) ^ 2) * log (exp u) ^ 2)) := by
    funext u
    simp only [log_exp, smul_eq_mul]
    ring
  rw [heq]
  exact integral_comp_exp (fun t : ℝ => exp (-t ^ 2) * log t ^ 2)

/-- The logarithm weighted Fourier profile is integrable.
Source book page 434, differentiated Plancherel prerequisite.
-/
theorem logWeightedGaussian_integrable (δ : ℝ) : Integrable (logWeightedGaussian δ) := by
  have hc := (gaussian_mellin_hasDerivAt δ (1 / 2) (by norm_num) (by norm_num)).1.norm
  have hg : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) *
      (|log t| * exp (-t ^ 2 / 2))) (Ioi 0) := by
    apply hc.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    have he := he0 (δ * t)
    simp only [norm_smul, norm_mul, he, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos ht]
    norm_num
  have hi := ((integrable_comp_exp (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) *
    (|log t| * exp (-t ^ 2 / 2)))).mpr hg).comp_neg
  apply hi.mono' (by unfold logWeightedGaussian logGaussian e; fun_prop)
  filter_upwards [] with u
  have he0 (v : ℝ) : ‖e v‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
  have he := he0 (δ * exp (-u))
  have hp : exp (-u) * (exp (-u)) ^ (-(1 / 2 : ℝ)) = exp (-u / 2) := by
    rw [← exp_mul, ← exp_add]
    congr 1
    ring
  rw [logWeightedGaussian, norm_smul, logGaussian, norm_smul, norm_mul, he, mul_one,
    Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_neg, log_exp, smul_eq_mul, abs_of_pos (exp_pos _)]
  rw [← hp]
  exact le_of_eq (by ring)

end LeanLab.HelfgottMajor.MellinDerivative431
