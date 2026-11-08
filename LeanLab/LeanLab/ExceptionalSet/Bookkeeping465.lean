import LeanLab.ExceptionalSet.SPLIT_leaf_odd_moment_upper

/-!
Finite bookkeeping companions for P0082 pages 366 to 369, displays 29 and 30.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open LeanLab.ExceptionalSet.U1539 (nu)

/-- P0082 pages 366 to 369, finite window bookkeeping.
Exact sealed leaf_odd_upper_window_split statement. -/
theorem odd_upper_window_split_supplied (N : ℕ) (hN : 100 ≤ N) :
    Finset.Icc ((N + 1) / 2 + N / 4 + 1) N =
      Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2) ∪
        Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N := by
  have haN : (N + 1) / 2 + N / 4 + 1 ≤ N := by omega
  have hbN : ((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 ≤ N := by omega
  ext n
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- P0082 pages 366 to 369, finite window bookkeeping.
Exact sealed leaf_odd_upper_window_disjoint statement. -/
theorem odd_upper_window_disjoint_supplied (γ : ℝ) (N : ℕ) :
    Disjoint
      ((Finset.Icc ((N + 1) / 2 + N / 4 + 1)
          (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2)).filter
        (fun n : ℕ => Odd (nu γ n)))
      ((Finset.Icc (((N + 1) / 2 + N / 4 + 1) + (N - ((N + 1) / 2 + N / 4 + 1)) / 2 + 1) N).filter
        (fun n : ℕ => Odd (nu γ n))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hn hm
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn hm
  omega

/-- P0082 pages 366 to 369, finite window bookkeeping.
Exact sealed leaf_odd_moment_add_const statement. -/
theorem odd_moment_add_const_supplied (M x y A B : ℝ) (hM : 0 ≤ M)
    (hx : x ≤ A * M) (hy : y ≤ B * M) : x + y ≤ (A + B + 1) * M := by
  nlinarith

end LeanLab.ExceptionalSet.Supply465
