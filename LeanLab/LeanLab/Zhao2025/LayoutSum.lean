import LeanLab.Zhao2025.Display110

/-!
The finite head and tail indices identify the layout energy with the sum of S squared.
Source: Zhao 2025, displays 2.28, 2.29, 4.10 and 4.11, pages 7 and 14.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- Number of unchanged head entries in the selected layout. -/
def headCount (k : Fin 11) (n : ℕ) : ℕ :=
  if k.val < 4 then n + 1 else if k.val = 4 then 2 else if k.val = 5 then 1 else 0

/-- Number of entries represented as R plus T. -/
def tailCount (k : Fin 11) (n : ℕ) : ℕ := if k.val < 4 then 0 else n

/-- The actual finite index type includes each head and each tail once. -/
abbrev LayoutIndex (k : Fin 11) (n : ℕ) := Fin (headCount k n) ⊕ Fin (tailCount k n)

/-- S is unchanged at a head and is defined as R plus T at a tail. -/
noncomputable def layoutS (k : Fin 11) (n : ℕ) (R T S : ℕ → ℝ) : LayoutIndex k n → ℝ :=
  Sum.elim (fun i => S i.val) (fun i => R i.val + T i.val)

/-- Reindexing the layout introduces no analytic assumption. -/
theorem layout_square_sum (k : Fin 11) (n : ℕ) (R T S : ℕ → ℝ) :
    ∑ i : LayoutIndex k n, layoutS k n R T S i ^ 2 = layoutEnergy k n R T S := by
  change (∑ i : Fin (headCount k n) ⊕ Fin (tailCount k n),
    Sum.elim (fun j => S j.val) (fun j => R j.val + T j.val) i ^ 2) = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun i => S i ^ 2) (headCount k n),
    Fin.sum_univ_eq_sum_range (fun i => (R i + T i) ^ 2) (tailCount k n)]
  fin_cases k <;>
    norm_num [headCount, tailCount, layoutEnergy, Finset.sum_range_succ] <;> ring

#print axioms layout_square_sum

end LeanLab.Zhao2025.Task56
