import LeanLab.HelfgottMajor.Decomp511b

/-!
P0014 page 26, display 3.65.
The endpoint ray has linear exponential damping when delta is positive.
Source: https://arxiv.org/abs/1305.2897
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Ray640Endpoint
open Real MeasureTheory Set Filter
open scoped Topology
open LeanLab.HelfgottMajor.Decomp511b

/-- LEAF: Exact modulus on the ray of angle pi over four.
P0014 page 26 display 3.65, with absolute ell equal to two pi delta. -/
theorem endpoint_kernel_norm (δ x : ℝ) (s : ℂ) (hx : 0 < x) :
    ‖rotatedKernel δ (π / 4) s x‖ =
      x ^ (s.re - 1) * exp (-((2 * π * δ * (sqrt 2 / 2)) * x)) := by
  rw [rotatedKernel_norm δ (π / 4) s x hx]
  rw [show 2 * (π / 4) = π / 2 by ring, cos_pi_div_two, sin_pi_div_four]
  congr 2
  ring

/-- LEAF: Absolute convergence and the exact Gamma bound on the endpoint ray.
P0014 page 26 display 3.65. This estimates the ray integral itself. -/
theorem endpoint_ray_majorant (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re) :
    IntegrableOn (rotatedKernel δ (π / 4) s) (Ioi 0) ∧
      ‖Complex.exp (((π / 4 : ℝ) : ℂ) * Complex.I * s) *
          (∫ x : ℝ in Ioi 0, rotatedKernel δ (π / 4) s x)‖ ≤
        (1 / (2 * π * δ * (sqrt 2 / 2))) ^ s.re * Gamma s.re *
          exp (-(π / 4) * s.im) := by
  let b := 2 * π * δ * (sqrt 2 / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * exp (-(b * x))) (Ioi 0) := by
    simpa only [rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := (1 : ℝ))
        (b := b) (by linarith) (by norm_num) hb)
  have hm : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      ‖rotatedKernel δ (π / 4) s x‖ ≤ x ^ (s.re - 1) * exp (-(b * x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (endpoint_kernel_norm δ x s hx).le
  have hi : IntegrableOn (rotatedKernel δ (π / 4) s) (Ioi 0) := by
    apply hg.mono' _ hm
    have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (s - 1)) (Ioi 0) :=
      Complex.continuous_ofReal.continuousOn.cpow_const
        (fun x hx => Complex.ofReal_mem_slitPlane.mpr hx)
    apply (hc.mul ?_).aestronglyMeasurable measurableSet_Ioi
    apply Continuous.continuousOn
    fun_prop
  refine ⟨hi, ?_⟩
  rw [norm_mul, rotated_prefactor_norm]
  calc
    _ ≤ exp (-(π / 4) * s.im) *
        (∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * exp (-(b * x))) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hg hm) (exp_nonneg _)
    _ = _ := by rw [integral_rpow_mul_exp_neg_mul_Ioi hσ hb]; ring

/-- LEAF: Linear damping uniformly dominates rays approaching the endpoint.
P0014 page 26 display 3.65. Angles stay between pi over eight and pi over four. -/
theorem near_endpoint_majorant (δ θ x : ℝ) (s : ℂ) (hδ : 0 ≤ δ) (hx : 0 < x)
    (hθ0 : π / 8 ≤ θ) (hθ1 : θ ≤ π / 4) :
    ‖rotatedKernel δ θ s x‖ ≤
      x ^ (s.re - 1) * exp (-((2 * π * δ * sin (π / 8)) * x)) := by
  rw [rotatedKernel_norm δ θ s x hx]
  apply mul_le_mul_of_nonneg_left _ (rpow_nonneg hx.le _)
  apply exp_le_exp.mpr
  have hc : 0 ≤ cos (2 * θ) := cos_nonneg_of_mem_Icc
    ⟨by linarith [pi_pos], by linarith⟩
  have hs : sin (π / 8) ≤ sin θ := sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [pi_pos]) (by linarith [pi_pos]) hθ0
  have hd : 0 ≤ 2 * π * δ * x := by positivity
  nlinarith [mul_nonneg hc (sq_nonneg x), mul_le_mul_of_nonneg_left hs hd]

/-- LEAF: Dominated convergence of the actual ray integrals at angle pi over four.
P0014 page 26 display 3.65. Positive twist supplies a uniform linear exponential majorant. -/
theorem endpoint_ray_limit (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re) :
    Tendsto (fun θ : ℝ => ∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x)
      (𝓝[<] (π / 4)) (𝓝 (∫ x : ℝ in Ioi 0, rotatedKernel δ (π / 4) s x)) := by
  let b := 2 * π * δ * sin (π / 8)
  have hb : 0 < b := by
    dsimp [b]
    exact mul_pos (by positivity)
      (sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos]))
  have hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * exp (-(b * x))) (Ioi 0) := by
    simpa only [rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := (1 : ℝ))
        (b := b) (by linarith) (by norm_num) hb)
  have hnear : Ioo (π / 8) (π / 4) ∈ 𝓝[<] (π / 4) :=
    Ioo_mem_nhdsLT (by linarith [pi_pos])
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => x ^ (s.re - 1) * exp (-(b * x))) ?_ ?_ hg ?_
  · filter_upwards [hnear] with θ hθ
    have hcos : 0 < cos (2 * θ) := cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2]⟩
    have hphase : 0 ≤ δ * sin θ := mul_nonneg hδ.le
      (sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, pi_pos])
        (by linarith [hθ.2, pi_pos]))
    exact (rotated_ray_majorant δ θ s hσ hcos hphase).1.aestronglyMeasurable
  · filter_upwards [hnear] with θ hθ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact near_endpoint_majorant δ θ x s hδ.le hx hθ.1.le hθ.2.le
  · apply Filter.Eventually.of_forall
    intro x
    have hc : Continuous (fun θ : ℝ => rotatedKernel δ θ s x) := by
      unfold rotatedKernel
      fun_prop
    exact hc.continuousAt.mono_left nhdsWithin_le_nhds

/-- LEAF: The exact endpoint ray rotation by a limit of interior rotations.
P0014 page 26 display 3.65. This identifies the endpoint ray with the original transform. -/
theorem positive_endpoint_rotation (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) :
    LeanLab.HelfgottMajor.SplitGaussian123.gaussianMellin δ s =
      Complex.exp (((π / 4 : ℝ) : ℂ) * Complex.I * s) *
        (∫ x : ℝ in Ioi 0, rotatedKernel δ (π / 4) s x) := by
  have hc : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I * s)) := by
    fun_prop
  have hl := (hc.continuousAt.mono_left nhdsWithin_le_nhds).mul
    (endpoint_ray_limit δ s hδ hσ)
  have heq : (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I * s) *
      (∫ x : ℝ in Ioi 0, rotatedKernel δ θ s x)) =ᶠ[𝓝[<] (π / 4)]
      (fun _ => LeanLab.HelfgottMajor.SplitGaussian123.gaussianMellin δ s) := by
    filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : (0 : ℝ) < π / 4)] with θ hθ
    exact (positive_ray_rotation δ θ s hδ hσ ht hθ.1 hθ.2).symm
  exact tendsto_nhds_unique tendsto_const_nhds (hl.congr' heq)

/-- LEAF: Display 3.65 as a bound on the original Gaussian Mellin transform.
P0014 page 26, positive delta and positive height. -/
theorem positive_endpoint_bound (δ : ℝ) (s : ℂ) (hδ : 0 < δ) (hσ : 0 < s.re)
    (ht : 100 ≤ s.im) :
    ‖LeanLab.HelfgottMajor.SplitGaussian123.gaussianMellin δ s‖ ≤
      (1 / (2 * π * δ * (sqrt 2 / 2))) ^ s.re * Gamma s.re *
        exp (-(π / 4) * s.im) := by
  rw [positive_endpoint_rotation δ s hδ hσ ht]
  exact (endpoint_ray_majorant δ s hδ hσ).2

end LeanLab.HelfgottMajor.Ray640Endpoint
