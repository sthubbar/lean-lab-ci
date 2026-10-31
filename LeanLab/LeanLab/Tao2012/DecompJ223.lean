import Mathlib
import LeanLab.Tao2012.Decomp1555a
import LeanLab.Tao2012.Cor48

namespace LeanLab.Tao2012.DecompJ223

open Real Finset MeasureTheory
open LeanLab.Tao2012.Decomp1555
open LeanLab.Tao2012.Cor48

/-- The cutoff function `1_{[0, 1]}`. -/
noncomputable def one_Icc : ℝ → ℝ := fun t => if t ∈ Set.Icc (0:ℝ) 1 then 1 else 0

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. The fundamental theorem of calculus
rewrites the smooth cutoff `η(n/x)` as the integral of `- (1/x) η'(y/x)` on `[n, x]`. -/
theorem eta_eq_integral (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : (n : ℝ) ≤ x) :
    η (n / x) = - (1 / x) * ∫ y in (n:ℝ)..x, deriv η (y / x) := by
  have H : ∫ y in (n:ℝ)..x, deriv (fun y => η (y / x)) y = η (x / x) - η (n / x) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => η (y / x)) (f' := fun y => deriv (fun y => η (y / x)) y)
    · intro y _
      exact (ContDiff.differentiable h_diff (by decide) |>.comp (differentiable_id.div_const x)).differentiableAt.hasDerivAt
    · exact ((ContDiff.continuous_deriv (h_diff.comp (contDiff_id.div_const x)) (by decide)).intervalIntegrable _ _)
  have hc : Continuous η := h_diff.continuous
  have eta_1_eq_0 : η 1 = 0 := by
    have h2 : Filter.Tendsto η (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds 0) := by
      have h_eq : ∀ᶠ x_1 in nhdsWithin (1:ℝ) (Set.Ioi 1), (fun _ => (0:ℝ)) x_1 = η x_1 := by
        apply Filter.eventually_iff_exists_mem.mpr
        use Set.Ioi 1
        constructor
        · exact self_mem_nhdsWithin
        · intro x_1 hx_1
          have : x_1 ∉ Set.Icc (0:ℝ) 1 := by
            intro h
            have hx_gt : x_1 > 1 := hx_1
            have hx_le : x_1 ≤ 1 := h.2
            linarith
          have : x_1 ∉ Function.support η := fun h => this (h_supp h)
          exact (not_not.mp this).symm
      exact Filter.Tendsto.congr' h_eq tendsto_const_nhds
    have h3 : Filter.Tendsto η (nhdsWithin (1:ℝ) (Set.Ioi 1)) (nhds (η 1)) := hc.tendsto 1 |>.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h3 h2
  have hx_pos : 0 < x := by linarith
  have h_x_div_x : x / x = 1 := div_self (ne_of_gt hx_pos)
  have H2 : ∫ y in (n:ℝ)..x, (1 / x) * deriv η (y / x) = η (x / x) - η (n / x) := by
    have H_deriv : ∀ y, deriv (fun y => η (y / x)) y = (1 / x) * deriv η (y / x) := by
      intro y
      have h_diff_eta : DifferentiableAt ℝ η (y / x) := (ContDiff.differentiable h_diff (by decide)).differentiableAt
      have h_diff_div : DifferentiableAt ℝ (fun y => y / x) y := (differentiable_id.div_const x).differentiableAt
      have : deriv (fun y => η (y / x)) y = deriv η (y / x) * deriv (fun y => y / x) y :=
        HasDerivAt.deriv (HasDerivAt.comp y h_diff_eta.hasDerivAt h_diff_div.hasDerivAt)
      rw [this]
      have h_div : deriv (fun y => y / x) y = 1 / x := by
        have H_id : deriv (fun y => y / x) y = deriv (fun y => y * (1 / x)) y := by
          congr 1
          ext y_1
          ring
        rw [H_id, deriv_mul_const differentiable_id.differentiableAt]
        have H_id_eval : deriv (fun y => y) y = 1 := deriv_id y
        rw [H_id_eval]
        ring
      rw [h_div]
      ring
    simp_rw [H_deriv] at H
    exact H
  rw [h_x_div_x, eta_1_eq_0] at H2
  have h_int : ∫ y in (n:ℝ)..x, (1 / x) * deriv η (y / x) = (1 / x) * ∫ y in (n:ℝ)..x, deriv η (y / x) := by
    exact intervalIntegral.integral_const_mul (1 / x) (fun y => deriv η (y / x))
  rw [h_int] at H2
  linarith

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. Summation by parts identity for `S`.
This substitutes the integral form of `η(n/x)` and exchanges the sum and the integral. -/
theorem S_eq_integral (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) :
    S η q ⌊x⌋₊ x α = - (1 / x) * ∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α := by
  sorry

/-- LEAF. Tao 2012, page 16, Lemma 4.2 proof. The integral norm inequality.
The norm of the integral is bounded by the integral of the norm, which is then bounded by
taking the supremum over the truncated sums. -/
theorem norm_S_le (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (x α : ℝ) (hx : 1 ≤ x) :
    ‖- (1 / x) * ∫ y in (0:ℝ)..x, ((deriv η (y / x) : ℝ) : ℂ) * S one_Icc q ⌊y⌋₊ y α‖ ≤
      (∫ t, |deriv η t|) * ⨆ y ∈ Set.Icc 0 x, ‖S one_Icc q ⌊y⌋₊ y α‖ := by
  sorry

/-- CITED. Tao 2012, page 16, Lemma 4.2, summation by parts for the smoothed prime sum.
Assembled from its leaves with no sorry. -/
theorem lemma4_2 (η : ℝ → ℝ) (h_diff : ContDiff ℝ 1 η) (h_supp : Function.support η ⊆ Set.Icc 0 1)
    (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hx : 1 ≤ x) (α : ℝ) :
      ‖S η q ⌊x⌋₊ x α‖ ≤ (∫ t, |deriv η t|) * ⨆ y ∈ Set.Icc 0 x, ‖S one_Icc q ⌊y⌋₊ y α‖ := by
  rw [S_eq_integral η h_diff h_supp q x α hx]
  exact norm_S_le η h_diff h_supp q x α hx

end LeanLab.Tao2012.DecompJ223
