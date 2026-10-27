import LeanLab.GoldbachAverage.FloorVariance82
import LeanLab.GoldbachAverage.GSTheorem1

/-!
The weighted prefix identity in P0051 page 10 eq. 53.
The proof uses Mathlib Abel summation.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.WeightedPrefix82
open Finset MeasureTheory
open FloorVariance82

/-- The weighted positive index coefficient prefix in eq. 53 page 10. -/
def weightedPrefix (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, Real.exp (-(n : ℝ) / N) * cfr n

/-- The cumulative coefficient sum is the counting function R, eq. 50 page 10. -/
theorem cfr_prefix {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Icc 0 ⌊x⌋₊, cfr n = psiFloorError x := by
  have hs : ∀ m : ℕ, (∑ n ∈ range (m + 1), if n = 0 then (0 : ℝ) else 1) = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; simp
  have hf : (⌊x⌋₊ : ℝ) = (⌊x⌋ : ℝ) := by exact_mod_cast Int.natCast_floor_eq_floor hx
  simp only [cfr, sum_sub_distrib]
  rw [← Chebyshev.psi_eq_sum_Icc, psiFloorError_eq,
    ← Nat.range_succ_eq_Icc_zero, hs, hf]

/-- LEAF. P0051 page 10 eq. 53, the exponentially weighted Abel identity. -/
theorem weighted_prefix_abel (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    weightedPrefix N x = psiFloorError x * Real.exp (-x / N) +
      1 / (N : ℝ) * ∫ t in (0 : ℝ)..x, psiFloorError t * Real.exp (-t / N) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t / N)
  have hd (t : ℝ) : HasDerivAt f (-(1 / (N : ℝ)) * f t) t := by
    have h := (Real.hasDerivAt_exp (-t / N)).comp t ((hasDerivAt_id t).neg.div_const (N : ℝ))
    simpa [f, Function.comp_def, neg_div, mul_comm] using h
  have hder (t : ℝ) : deriv f t = -(1 / (N : ℝ)) * f t := (hd t).deriv
  have hc : Continuous (deriv f) := by
    change Continuous (fun t => deriv f t)
    simp_rw [hder]
    dsimp [f]
    fun_prop
  have hb := sum_mul_eq_sub_integral_mul cfr hx
    (fun t _ => (hd t).differentiableAt) hc.integrableOn_Icc
  rw [cfr_prefix hx, ← intervalIntegral.integral_of_le hx] at hb
  have he : (∫ t in (0 : ℝ)..x, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, cfr n) =
      -(1 / (N : ℝ)) * ∫ t in (0 : ℝ)..x, psiFloorError t * f t := by
    calc (∫ t in (0 : ℝ)..x, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, cfr n) =
        ∫ t in (0 : ℝ)..x, -(1 / (N : ℝ)) * (psiFloorError t * f t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hx] at ht
          dsimp only
          rw [hder, cfr_prefix ht.1]
          ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [he] at hb
  calc weightedPrefix N x = f x * psiFloorError x -
        (-(1 / (N : ℝ)) * ∫ t in (0 : ℝ)..x, psiFloorError t * f t) := hb
    _ = _ := by dsimp [f]; ring

end LeanLab.GoldbachAverage.WeightedPrefix82
