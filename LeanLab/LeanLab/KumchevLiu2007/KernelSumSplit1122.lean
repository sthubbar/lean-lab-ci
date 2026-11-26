/-
ROUTE BURST burst-20261122, session S81. SPLIT of the LEAF Burst1122B27.kernel_sum_bound,
P0088 Kumchev and Liu 2007, page 7, the display before 27, QUESTION Q2.

FINDING on the reading of the leaf: primeWindow X Y of Task556a is the set of ALL integers m
with X - Y at most m below X, with no primality test; T1 is the smooth sum with weight
1/log m. So no short interval prime number theorem is needed and no Huxley input enters.
The leaf is purely elementary. The split is:
1. kernel_sum_swap, PROVED: the double sum is bounded by the sum over m2 of
   |f2Weight| times |innerSum|, the inner sum over m1 of K against 1/log m1.
2. inner_window_bound, LEAF MEDIUM: |innerSum| at most C times edgeDecay / log X plus Y / X,
   from the vanishing total mass of K, Abel summation of sin, and partial summation in 1/log.
3. outer_square_bound, LEAF MEDIUM: the sum over m2 of |f2Weight| times that bound is
   O(Y^(1/2) P^(-2)), from the spacing of squares near the two window edges.
kernel_sum_bound_of_pieces proves the exact type of kernel_sum_bound from the two leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Bound27Split1122
import LeanLab.KumchevLiu2007.KernelBase687
import LeanLab.KumchevLiu2007.KernelEdge687
import LeanLab.KumchevLiu2007.KernelInner687

namespace LeanLab.KumchevLiu2007.KernelSumSplit1122

open Real LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- PROVED from the two leaves above: the exact type of Burst1122B27.kernel_sum_bound. -/
theorem kernel_sum_bound_of_pieces
    (hin : ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∃ C X0 : ℝ, 0 < C ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n m2 : ℕ,
        m2 ∈ squareWindow (windowY X ε) →
        |innerSum X (windowY X ε) (bq X ε B q) n m2| ≤
          C * (edgeDecay X (windowY X ε) (bq X ε B q) n m2 / Real.log X + windowY X ε / X))
    (hout : ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ C : ℝ, 0 < C → ∃ C' X0 : ℝ, 0 < C' ∧
      ∀ X : ℝ, X0 ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B → ∀ n : ℕ,
        ∑ m2 ∈ squareWindow (windowY X ε),
            |f2Weight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m2 : ℝ)| *
              (C * (edgeDecay X (windowY X ε) (bq X ε B q) n m2 / Real.log X + windowY X ε / X)) ≤
          C' * Real.sqrt (windowY X ε) * (Real.log X ^ B) ^ (-2 : ℤ)) :
    type_of% @Burst1122B27.kernel_sum_bound := by
  intro B hB ε hε hε'
  obtain ⟨C, X1, hC, hI⟩ := hin B hB ε hε hε'
  obtain ⟨C', X2, hC', hO⟩ := hout B hB ε hε hε' C hC
  refine ⟨C', max X1 X2, hC', fun X hX q hq1 hqP n => ?_⟩
  have h1 : X1 ≤ X := le_trans (le_max_left _ _) hX
  have h2 : X2 ≤ X := le_trans (le_max_right _ _) hX
  refine le_trans ?_ (hO X h2 q hq1 hqP n)
  refine le_trans (le_of_eq ?_) ((kernel_sum_swap X (windowY X ε)
    (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (bq X ε B q) n).trans
    (Finset.sum_le_sum fun m2 hm2 => mul_le_mul_of_nonneg_left
      (hI X h1 q hq1 hqP n m2 hm2) (abs_nonneg _)))
  rfl

/-- PROVED: the leaf follows from the two leaves of this file. -/
theorem kernel_sum_bound_split : type_of% @Burst1122B27.kernel_sum_bound :=
  kernel_sum_bound_of_pieces inner_window_bound outer_square_bound

end LeanLab.KumchevLiu2007.KernelSumSplit1122

#print axioms LeanLab.KumchevLiu2007.KernelSumSplit1122.kernel_sum_swap
#print axioms LeanLab.KumchevLiu2007.KernelSumSplit1122.kernel_sum_bound_of_pieces
#print axioms LeanLab.KumchevLiu2007.KernelSumSplit1122.kernel_sum_bound_split
