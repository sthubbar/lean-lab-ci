import LeanLab.GoldbachAverage.Decomp124

/-!
The remaining thin prime set statements on P0098 page 163.
These are cited propositions. No proof of either proposition is asserted here.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.State124
open Filter Set
open Classical Decomp124

/-- The exceptional even integers at least four up to x that lack a pair from P.
Source: the exception counts in P0098 Theorem 3 and its corollary, page 163. -/
def badEven (P : Set ℕ) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun n => Even n ∧ 2 < n ∧
    ¬ ∃ p ∈ P, ∃ q ∈ P, p + q = n).card

/-- CITED. P0098 Theorem 3, page 163. Both bounds hold for sufficiently large real x.
The usual Goldbach range starts at four. -/
def GranvilleTheorem3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (κ : ℝ) (P : Set ℕ), 0 < κ ∧
    (∀ p ∈ P, Nat.Prime p) ∧
    ∀ᶠ x : ℝ in atTop,
      (count P x : ℝ) ≤ κ * Real.sqrt x ∧ (badEven P x : ℝ) ≤ ε * x

/-- CITED. P0098 corollary to Theorem 3, page 163.
The radical covers x only. The factor g x is outside the radical. -/
def GranvilleThinCorollary : Prop :=
  ∀ g : ℝ → ℝ, Tendsto g atTop atTop →
    ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧
      (∀ᶠ x : ℝ in atTop, (count P x : ℝ) ≤ Real.sqrt x * g x) ∧
      Tendsto (fun x : ℝ => (badEven P x : ℝ) / x) atTop (nhds 0)

end LeanLab.GoldbachAverage.State124
