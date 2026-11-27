import LeanLab.HelfgottMajor.SPLIT_negative_bottom_gaussian_lower_window_mid

/-!
Differentiation under the Mellin integral for the Gaussian Mellin transform F_delta, a step of
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 43, the proof of display
4.43, where F_delta is compared at nearby ordinates of the critical line. Shared by the splits of
the mid window Lipschitz leaves. A public form, for every positive real part, of the private
`gmellin_hasDerivAt` in `SPLIT_negative_mass_bulk_le`.

PROVED. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b Filter Asymptotics Topology

/-- PROVED: differentiation under the Mellin integral, P0014 page 43, proof of display 4.43: for
real part positive, F_delta has complex derivative the Mellin transform of `log x` times the
twisted Gaussian. From `mellin_hasDerivAt_of_isBigO_rpow`, the twisted Gaussian having norm
`exp (-x^2/2)`, at most `exp (-x)` for `x ≥ 2` and at most one near zero. -/
theorem gaussianMellin_hasDerivAt_log (δ : ℝ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (gaussianMellin δ)
      (mellin (fun x : ℝ => Real.log x • ((exp (-x ^ 2 / 2) : ℂ) * e (δ * x))) s) s := by
  set f : ℝ → ℂ := fun x => (exp (-x ^ 2 / 2) : ℂ) * e (δ * x) with hf
  have hnorm : ∀ x : ℝ, ‖f x‖ = Real.exp (-x ^ 2 / 2) := by
    intro x
    have he : ‖e (δ * x)‖ = 1 := by simp [e, Complex.norm_exp]
    simp only [hf, norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hcont : Continuous f := by
    simp only [hf, e]; fun_prop
  have hfc : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0) :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : f =O[atTop] fun t => Real.exp (-1 * t) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
    rw [hnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hbot : f =O[𝓝[>] 0] (· ^ (-(0:ℝ))) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hnorm, neg_zero, Real.rpow_zero, norm_one, one_mul]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hfc
    (htop.trans (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO) (lt_add_one _) hbot hs
  exact this.2

end LeanLab.HelfgottMajor.Decomp431a
