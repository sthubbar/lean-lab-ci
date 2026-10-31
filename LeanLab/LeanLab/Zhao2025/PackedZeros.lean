import LeanLab.Zhao2025.Display110Zeros

/-!
Extend a finite layout to natural indices using empty zero sets.
The infinite square sum is summable and equals the finite layout sum.
Source: Zhao 2025, displays 1.10 and 2.28, pages 3 and 7.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- A finite layout becomes a sequence by putting empty sets after its last entry. -/
def packedZeros {ι : Type*} (k : Fin 11) (n : ℕ) (H B : ℕ → Finset ι) (i : ℕ) : Finset ι :=
  if hi : i < headCount k n + tailCount k n then
    layoutZeros k n H B (finSumFinEquiv.symm ⟨i, hi⟩) else ∅

/-- Empty padding preserves the square sum and proves summability. -/
theorem packed_square_sum {ι : Type*} (k : Fin 11) (n : ℕ)
    (H B : ℕ → Finset ι) (lam : ι → ℝ) :
    Summable (fun i : ℕ => zeroSum (packedZeros k n H B i) lam ^ 2) ∧
    ∑' i : ℕ, zeroSum (packedZeros k n H B i) lam ^ 2 =
      ∑ i : LayoutIndex k n, zeroSum (layoutZeros k n H B i) lam ^ 2 := by
  have hz : ∀ i ∉ Finset.range (headCount k n + tailCount k n),
      zeroSum (packedZeros k n H B i) lam ^ 2 = 0 := by
    intro i hi
    have hni : ¬ i < headCount k n + tailCount k n := by simpa using hi
    simp [packedZeros, hni, zeroSum]
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz,
    ← Fin.sum_univ_eq_sum_range (fun i => zeroSum (packedZeros k n H B i) lam ^ 2)
      (headCount k n + tailCount k n)]
  simp only [packedZeros, Fin.is_lt, dite_true]
  exact Equiv.sum_comp finSumFinEquiv.symm
    (fun i : LayoutIndex k n => zeroSum (layoutZeros k n H B i) lam ^ 2)

#print axioms packed_square_sum

end LeanLab.Zhao2025.Task56
