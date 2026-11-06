import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
The center case of the Landau estimate cited on P0014 page 36, display 4.16.
The proof constructs an analytic logarithm and uses the Mathlib Schwarz lemma.
This does not supply the off center estimate used in display 4.17.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Landau309
open Complex Metric Set Filter
open scoped Topology

/-- A zero free holomorphic function on a disk has a normalized holomorphic logarithm.
This is the logarithm prerequisite in the proof of display 4.16 on P0014 page 36.
-/
theorem normalized_log_exists (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 R) ∧ g 0 = 0 ∧
      ∀ z ∈ ball 0 R, exp (g z) = f z / f 0 := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hf0 := hn 0 h0
  letI : ContractibleSpace (ball (0 : ℂ) R) :=
    (convex_ball (0 : ℂ) R).contractibleSpace ⟨0, h0⟩
  have hsc : IsSimplyConnected (ball (0 : ℂ) R) := by
    change SimplyConnectedSpace (ball (0 : ℂ) R)
    infer_instance
  have hc : ContinuousOn (fun z => f z / f 0) (ball 0 R) :=
    hf.continuousOn.div_const _
  have hne : 0 ∉ (fun z => f z / f 0) '' ball 0 R := by
    rintro ⟨z, hz, he⟩
    exact (div_ne_zero (hn z hz) hf0) he
  obtain ⟨u, huc, hue⟩ := exists_continuousOn_eqOn_exp_comp hsc isOpen_ball hc hne
  have hud : DifferentiableOn ℂ u (ball 0 R) := by
    intro z hz
    have hct := huc.continuousAt (isOpen_ball.mem_nhds hz)
    have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.div_const (f 0)
    have he : exp ∘ u =ᶠ[𝓝 z] fun w => f w / f 0 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hue hw
    exact (HasDerivAt.of_comp_left hct (hasDerivAt_exp (u z)) hfd
      (exp_ne_zero _) he).differentiableAt.differentiableWithinAt
  refine ⟨fun z => u z - u 0, hud.sub_const _, by simp, ?_⟩
  intro z hz
  have hez : exp (u z) = f z / f 0 := hue hz
  have he0 : exp (u 0) = f 0 / f 0 := hue h0
  rw [exp_sub, hez, he0, div_self hf0, div_one]

/-- The center derivative estimate for a normalized holomorphic function with bounded real part.
Source P0014 page 36 display 4.16, the Borel Caratheodory step.
-/
theorem normalized_derivative_bound (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hgre : ∀ z ∈ ball 0 R, (g z).re ≤ M) :
    ‖deriv g 0‖ ≤ 2 * M / R := by
  let w : ℂ → ℂ := fun z => g z / (2 * (M : ℂ) - g z)
  have hd : ∀ z ∈ ball 0 R, 2 * (M : ℂ) - g z ≠ 0 := by
    intro z hz he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    norm_num at hr
    linarith [hgre z hz]
  have hwd : DifferentiableOn ℂ w (ball 0 R) := hg.div (hg.const_sub _) hd
  have hw0 : w 0 = 0 := by simp [w, hg0]
  have hmaps : MapsTo w (ball 0 R) (closedBall (w 0) 1) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm_sub, hw0, sub_zero]
    dsimp [w]
    rw [norm_div]
    have hnorm : ‖g z‖ ≤ ‖2 * (M : ℂ) - g z‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      suffices (g z).re * (g z).re ≤ (2 * M - (g z).re) * (2 * M - (g z).re) by
        simpa [Complex.sq_norm, normSq_apply] using this
      nlinarith [hgre z hz]
    exact div_le_one_of_le₀ hnorm (norm_nonneg _)
  have hb := norm_deriv_le_div_of_mapsTo_ball hwd hmaps hR
  have hgd := (hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
  have hden : 2 * (M : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hM.ne')
  have hwder : HasDerivAt w (deriv g 0 / (2 * (M : ℂ))) 0 := by
    convert hgd.div (hgd.const_sub (2 * (M : ℂ))) (hd 0 (mem_ball_self hR)) using 1 <;>
      simp [w, hg0] <;> field_simp <;> ring
  rw [hwder.deriv, norm_div, norm_mul, norm_ofNat, norm_real,
    Real.norm_of_nonneg hM.le] at hb
  have hb' := (div_le_iff₀ (by positivity : 0 < 2 * M)).mp hb
  calc ‖deriv g 0‖ ≤ 1 / R * (2 * M) := hb'
    _ = 2 * M / R := by ring

/-- Landau at the center of the zero free disk, the r equal to zero case of display 4.16.
The strict upper budget makes the logarithm positive. No cited analytic input remains.
-/
theorem landau_center (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hM : ‖f 0‖ < M) (hbound : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M) :
    ‖logDeriv f 0‖ ≤ 2 * Real.log (M / ‖f 0‖) / R := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hf0 := hn 0 h0
  have hn0 : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  obtain ⟨g, hgd, hg0, hge⟩ := normalized_log_exists f R hR hf hn
  have hlog : 0 < Real.log (M / ‖f 0‖) :=
    Real.log_pos ((one_lt_div hn0).mpr hM)
  have hgre : ∀ z ∈ ball 0 R, (g z).re ≤ Real.log (M / ‖f 0‖) := by
    intro z hz
    have he := congrArg norm (hge z hz)
    rw [norm_exp, norm_div] at he
    have he' : (g z).re = Real.log (‖f z‖ / ‖f 0‖) := by
      rw [← he, Real.log_exp]
    rw [he']
    apply Real.log_le_log (div_pos (norm_pos_iff.mpr (hn z hz)) hn0)
    exact div_le_div_of_nonneg_right (hbound z hz) hn0.le
  have hgder := (hgd.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
  have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt.div_const (f 0)
  have he : exp ∘ g =ᶠ[𝓝 (0 : ℂ)] fun z => f z / f 0 := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact hge z hz
  have heq := hgder.cexp.unique (hfd.congr_of_eventuallyEq he)
  simp only [hg0, exp_zero, one_mul] at heq
  rw [logDeriv_apply, ← heq]
  exact normalized_derivative_bound g R _ hR hlog hgd hg0 hgre

end LeanLab.HelfgottMajor.Landau309
