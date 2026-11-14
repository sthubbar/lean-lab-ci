/-
Jia 1996 page 253, Lemma 17.
Source https://doi.org/10.4064/aa-77-3-207-287.
The progression input used by the Iwaniec transfer remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565

namespace LeanLab.Languasco2004.Decomp565c
open Finset Real Decomp279a Source565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 253 Lemma 17: count the prime progressions with ml at most twice Y. -/
def progressionCount (N Y : ℝ) (n m : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun a => m ∣ a ∧ (a : ℝ) ≤ 2 * Y ∧
    (n - a).Prime ∧ N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N)).card

/-- Page 253 Lemma 17: the dyadic weighted progression remainder. -/
def progressionRemainder (N Y M : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ (range (n + 1)).filter (fun m : ℕ =>
    M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M ∧ Nat.Coprime m n),
    a m * ((progressionCount N Y n m : ℝ) - Y / ((Nat.totient m : ℝ) * log N))

/-- LEAF. Jia page 253, Lemma 17, unnumbered displayed estimate.
The written proof invokes Lemmas 6 and 15. This is the bounded weight and
M at most Y to the power 19/36 specialization needed by display 58 on page 283.
Both big O constants are retained. The exceptional estimate remains OPEN. -/
theorem lemma17_progression_input :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ M : ℝ → ℝ, ∀ a : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N → 1 ≤ M N ∧ M N ≤ (localization N ε) ^ (19 / 36 : ℝ)) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * localization N ε / log N ^ B <
          |progressionRemainder N (localization N ε) (M N) n (a N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by sorry

/-- Page 253: zero weights give a nonempty parameter domain without claiming the analytic input. -/
theorem progression_zero_weights (N Y M : ℝ) (n : ℕ) :
    progressionRemainder N Y M n (fun _ => 0) = 0 := by
  simp [progressionRemainder]

#print axioms lemma17_progression_input
#print axioms progression_zero_weights
end
end LeanLab.Languasco2004.Decomp565c
