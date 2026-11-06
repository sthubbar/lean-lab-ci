/-
P0079 page 9, the discrete intermediary in the written J3 proof.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp375b

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 8, before Lemma 6. U is the unweighted integer sum
on the same interval as the prime sum. -/
def discretePrime396 (ε X α : ℝ) : ℂ :=
  ∑ n ∈ (range (⌊X⌋₊ + 1)).filter (fun n : ℕ => ε * X ≤ (n : ℝ)),
    character293 (n * α)

/-- P0079 page 9, the J3 integral with S minus U. This intermediate
integrand replaces only the second prime sum by the integer sum U. -/
def discreteSecondModel396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) * discretePrime396 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

end LeanLab.LZPowersOfTwo
