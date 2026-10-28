/-
Tao 2012, Lemma 4.2.
-/
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
  sorry

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
