/-
P0069 page 8, displays 2.8 and 2.9.
A shared short interval arithmetic input and the two exact tail conclusions.
This file does not import Decomp512a or its importers.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561a
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace LeanLab.BHP1997.Decomp561b
open Finset Decomp561a

/-- P0069 page 3, the short frequency interval length H. -/
noncomputable def intervalLength561 (ε x : ℝ) : ℝ :=
  x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
/-- P0069 page 6, the even frequencies in K, expanded independently of the sealed file. -/
noncomputable def frequencies561 (ε x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + intervalLength561 ε x⌋₊).filter (fun N : ℕ => Even N)

/-- LEAF. P0069 page 8 displays 2.8 and 2.9, short interval arithmetic input.
A fourth divisor moment replaces the printed second moment because the proved
pointwise envelope uses tau in place of a logarithmic totient ratio bound.
Only the unweighted short interval moment remains. No cutoff parameter occurs.
The exponent 16 is a sufficient auxiliary bound, not a printed constant. OPEN. -/
theorem leaf_short_interval_divisor_fourth_moment561 :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      (∑ N ∈ frequencies561 ε x, (N.divisors.card : ℝ) ^ 4) ≤
        C * intervalLength561 ε x * Real.log x ^ (16 : ℝ) := by
  sorry

/-- P0069 page 8 displays 2.8 and 2.9, absorb the common cutoff into any requested
logarithmic saving. CONDITIONAL ON the supplied unweighted fourth moment. -/
theorem moment_from_fourth (ε : ℝ) (w : ℝ → ℝ → ℕ → ℝ)
    (hfourth : ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      (∑ N ∈ frequencies561 ε x, (N.divisors.card : ℝ) ^ 4) ≤
        C * intervalLength561 ε x * Real.log x ^ (16 : ℝ))
    (hw0 : ∀ D x : ℝ, 3 ≤ x → ∀ N ∈ frequencies561 ε x, 0 ≤ w D x N)
    (hw : ∀ D x : ℝ, 3 ≤ x → ∀ N ∈ frequencies561 ε x,
      w D x N ≤ (N.divisors.card : ℝ) ^ 2 / Real.log x ^ (2 * D)) :
    ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x → (∑ N ∈ frequencies561 ε x, w D x N ^ 2) ≤
        C * intervalLength561 ε x * Real.log x ^ (-A - 7) := by
  intro A _hA
  obtain ⟨C₀, hC₀⟩ := hfourth
  refine ⟨(A + 23) / 4, fun D hD => ?_⟩
  let C : ℝ := max C₀ 3
  refine ⟨C, fun x hx => ?_⟩
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hxC : C₀ ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 1 ≤ Real.log x := by
    have he : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans_le (by norm_num)
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (he.le.trans hx3)
  have hlog0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog
  have hH : 0 ≤ intervalLength561 ε x := Real.rpow_nonneg hx0 _
  have hP : 0 < Real.log x ^ (2 * D) := Real.rpow_pos_of_pos hlog0 _
  calc
    _ ≤ (∑ N ∈ frequencies561 ε x, (N.divisors.card : ℝ) ^ 4) / (Real.log x ^ (2 * D)) ^ 2 :=
      tail_square_sum_le _ hP _ (hw0 D x hx3) (hw D x hx3)
    _ ≤ (C₀ * intervalLength561 ε x * Real.log x ^ (16 : ℝ)) / (Real.log x ^ (2 * D)) ^ 2 :=
      div_le_div_of_nonneg_right (hC₀ x hxC) (sq_nonneg _)
    _ ≤ (C * intervalLength561 ε x * Real.log x ^ (16 : ℝ)) / (Real.log x ^ (2 * D)) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hH)
        (Real.rpow_nonneg hlog0.le _)
    _ = C * intervalLength561 ε x * Real.log x ^ (16 - 4 * D) := by
      rw [← Real.rpow_mul_natCast hlog0.le, mul_div_assoc, ← Real.rpow_sub hlog0]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by dsimp [C]; positivity) hH)
      exact Real.rpow_le_rpow_of_exponent_le hlog (by linarith)

/-- P0069 page 8 display 2.8, the exact expanded statement of
leaf_small_divisor_moment512. CONDITIONAL ON the unweighted short interval leaf.
The sealed file remains untouched. -/
theorem small_divisor_moment561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          (∑ N ∈ frequencies561 ε x,
            (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.log x ^ (2 * D)),
              (d : ℝ) / (Nat.totient d : ℝ) / Real.log x ^ (2 * D)) ^ 2) ≤
          C * intervalLength561 ε x * Real.log x ^ (-A - 7) := by
  refine ⟨1 / 100, by norm_num, fun ε hε hε₀ => ?_⟩
  apply moment_from_fourth ε _ (leaf_short_interval_divisor_fourth_moment561 ε hε hε₀)
  · intro D x hx N hN
    have hP : 0 < Real.log x ^ (2 * D) := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  · intro D x hx N hN
    exact small_tail_le (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _) N

/-- P0069 page 8 display 2.9, the exact expanded statement of
leaf_large_divisor_moment512. CONDITIONAL ON the same unweighted arithmetic leaf.
No separate weighted tail estimate is assumed. -/
theorem large_divisor_moment561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          (∑ N ∈ frequencies561 ε x,
            (∑ d ∈ N.divisors.filter (fun d : ℕ => Real.log x ^ (2 * D) < (d : ℝ)),
              1 / (Nat.totient d : ℝ)) ^ 2) ≤
          C * intervalLength561 ε x * Real.log x ^ (-A - 7) := by
  refine ⟨1 / 100, by norm_num, fun ε hε hε₀ => ?_⟩
  apply moment_from_fourth ε _ (leaf_short_interval_divisor_fourth_moment561 ε hε hε₀)
  · intro D x hx N hN
    have hP : 0 < Real.log x ^ (2 * D) := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  · intro D x hx N hN
    exact large_tail_le (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _) N

end LeanLab.BHP1997.Decomp561b
