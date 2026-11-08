import LeanLab.ExceptionalSet.SPLIT_leaf_sum_large_N
import LeanLab.ExceptionalSet.SPLIT_leaf_odd_moment_upper

/-!
P0082 pages 367 and 371, elementary interval and exponent bookkeeping.
The analytic moment and cancellation inputs remain open.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464e

open Real MeasureTheory
open LeanLab.ExceptionalSet.U1539 (nu)

/-- P0082 page 371, scalar auxiliary for merging two ranges of orders. The cancellation input remains cited.
Exact clean companion for an elementary open leaf. -/
theorem leaf_exponent_mono (cA c : ℝ) (hc : 0 < c) (hcA : c ≤ cA) (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) (hk : 0 < k) :
    (N : ℝ) ^ (1 - cA / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hdiv := div_le_div_of_nonneg_right hcA (sq_nonneg (k : ℝ))
  linarith

/-- P0082 page 367 display 30, finite interval bookkeeping auxiliary. These midpoint choices belong to the formal split.
Exact clean companion for an elementary open leaf. -/
theorem leaf_odd_upper_window_split (N : ℕ) (hN : 100 ≤ N) :
    Finset.Icc ((N + 1) / 2 + N / 4 + 1) N =
      Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2) ∪
        Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- P0082 page 367 display 30, finite interval bookkeeping auxiliary.
Exact clean companion for an elementary open leaf. -/
theorem leaf_odd_upper_window_disjoint (γ : ℝ) (N : ℕ) :
    Disjoint
      ((Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2)).filter
        (fun n : ℕ => Odd (nu γ n)))
      ((Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N).filter
        (fun n : ℕ => Odd (nu γ n))) := by
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn hn'
  omega

/-- P0082 page 367 display 30, scalar auxiliary for adding two window bounds.
Exact clean companion for an elementary open leaf. -/
theorem leaf_odd_moment_add_const (M x y A B : ℝ) (hM : 0 ≤ M)
    (hx : x ≤ A * M) (hy : y ≤ B * M) : x + y ≤ (A + B + 1) * M := by
  nlinarith

end LeanLab.ExceptionalSet.Decomp464e
