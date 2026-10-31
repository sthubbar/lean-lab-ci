import LeanLab.Zhao2025.WeightedSqrtB
import LeanLab.Zhao2025.SmoothingWeight

/-!
The elementary final steps of Lemma 3.1 from display 3.8.
Estimate38 is the order form of the displayed maximum bound.
Its nonnegative envelope also handles the empty finite zero family.
Source: Zhao 2025, displays 3.3 and 3.8 to 3.11, pages 8 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

open LeanLab.Zhao2025.U6825

/-- The analytic input 3.8 expressed using any nonnegative envelope for its maximum. -/
def Estimate38 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (k x y z L l0 epsilon : ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
    (∀ j ∈ s, Real.exp (-((1 / 3 + x + y + z) / 2 * max (L - lam j) 0)) *
      Real.sqrt (B (1 / 3 + x + y) (lam j) l0 * B z (lam j) l0) ≤ M) →
    (∑ j ∈ s, smoothingWeight k ((1 / 3 + x + y + z) / 2) L (lam j)) ≤
      (1 + epsilon) * (1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)) * M

/-- CONDITIONAL ON display 3.8, with all remaining steps of Lemma 3.1 proved. -/
theorem lemma3_1_from38 {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (k x y z L l0 epsilon : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hL : 0 < L) (h0 : 0 ≤ l0) (hLam : ∀ j ∈ s, 0 < lam j)
    (hk : k = 2 * (1 / 3 + 3 * x + y + z) ∨ k = 2 * (2 / 3 + 3 * x + y + z))
    (h38 : Estimate38 s lam k x y z L l0 epsilon) :
    weightedCappedSum k s lam L ≤ (1 + epsilon) * C x y z L l0 := by
  have ha : (1 / 3 + x + y + z) / 2 ≤ k := by
    rcases hk with hk | hk <;> rw [hk] <;> linarith
  let M := Real.sqrt (B (1 / 3 + x + y) L l0 * B z L l0)
  have hrows : ∀ j ∈ s, Real.exp (-((1 / 3 + x + y + z) / 2 * max (L - lam j) 0)) *
      Real.sqrt (B (1 / 3 + x + y) (lam j) l0 * B z (lam j) l0) ≤ M := by
    intro j hj
    exact weighted_sqrt_B (1 / 3 + x + y) z (lam j) L l0
      (by linarith) hz.le (hLam j hj) hL h0
  have hw := h38 M (Real.sqrt_nonneg _) hrows
  have hcap : weightedCappedSum k s lam L ≤
      ∑ j ∈ s, smoothingWeight k ((1 / 3 + x + y + z) / 2) L (lam j) := by
    apply Finset.sum_le_sum
    intro j _
    exact smoothing_weight_lower k ((1 / 3 + x + y + z) / 2) L (lam j) ha
  unfold C
  calc
    _ ≤ _ := hcap
    _ ≤ (1 + epsilon) * (1 / (x * z) * (1 / 2 + (1 / 3 + x) / y)) * M := hw
    _ = _ := by dsimp [M]; ring

#print axioms lemma3_1_from38

end LeanLab.Zhao2025.Task56
