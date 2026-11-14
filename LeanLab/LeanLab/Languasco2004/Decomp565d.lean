/-
Jia 1996 page 260, Lemma 19.
Source https://doi.org/10.4064/aa-77-3-207-287.
The bounded rough weight input is stated separately from its region specializations.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565

namespace LeanLab.Languasco2004.Decomp565d
open Finset Real Decomp279a Decomp316a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 260 Lemma 19: count prime cofactors in the actual correlation or the model interval. -/
def cofactorCount (model : Bool) (N Y : ℝ) (n m : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    if model then Y < ((m * p : ℕ) : ℝ) ∧ ((m * p : ℕ) : ℝ) ≤ 2 * Y
    else m * p ≤ n ∧ ((m * p : ℕ) : ℝ) ≤ 2 * Y ∧ (n - m * p).Prime ∧
      N - Y < ((n - m * p : ℕ) : ℝ) ∧ ((n - m * p : ℕ) : ℝ) ≤ N)).card

/-- Page 260 Lemma 19: a nonnegative dyadic weight sum of the prime cofactor counts. -/
def weightedCofactors (model : Bool) (N Y M : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ (range (n + 1)).filter (fun m : ℕ => M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M),
    a m * (cofactorCount model N Y n m : ℝ)

/-- LEAF. Jia page 260, Lemma 19, unnumbered displayed asymptotic formula.
The written proof invokes Lemmas 5 and 18. The relative error of order
one divided by log N and the absolute error of order Y divided by log N to B
are both retained, with one positive constant bounding their two constants.
The weight is bounded by one and vanishes on integers with a prime factor below Y to delta.
This input underlies displays 59 and 63 on pages 283 and 284. -/
theorem lemma19_rough_input :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ M : ℝ → ℝ, ∀ a : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (119 / 135 : ℝ) ≤ M N ∧
          M N ≤ (localization N ε) ^ (1 - delta ε)) →
      (∀ N : ℝ, ∀ m : ℕ, 0 ≤ a N m ∧ a N m ≤ 1) →
      (∀ N : ℝ, 2 ≤ N → ∀ m p : ℕ, p.Prime → p ∣ m →
        (p : ℝ) < (localization N ε) ^ delta ε → a N m = 0) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * (singular n * weightedCofactors true N (localization N ε) (M N) n (a N) /
            log N ^ (2 : ℕ) + localization N ε / log N ^ B) <
          |weightedCofactors false N (localization N ε) (M N) n (a N) -
            singular n / log N * weightedCofactors true N (localization N ε) (M N) n (a N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by sorry

/-- Page 260: zero weights satisfy the rough support condition and give both counts zero. -/
theorem rough_zero_weights (N Y M : ℝ) (n : ℕ) :
    weightedCofactors false N Y M n (fun _ => 0) = 0 ∧
      weightedCofactors true N Y M n (fun _ => 0) = 0 := by
  simp [weightedCofactors]

#print axioms lemma19_rough_input
#print axioms rough_zero_weights
end
end LeanLab.Languasco2004.Decomp565d
