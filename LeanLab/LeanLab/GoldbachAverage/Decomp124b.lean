import LeanLab.GoldbachAverage.State124

/-!
P0098 Theorem 3, statement page 163, written proof page 167.
The external almost all rich Goldbach result and the sampling selection remain cited.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp124b
open Classical Filter Set
open Decomp124 State124

/-- Even integers in the Goldbach range outside the rich set, P0098 page 167. -/
def poorEven (γ x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun n => Even n ∧ 2 < n ∧ n ∉ richEven γ).card

/-- Rich integers with no representation from P, P0098 page 167. -/
def missedRich (P : Set ℕ) (γ x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun n => n ∈ richEven γ ∧
    ¬ ∃ p ∈ P, ∃ q ∈ P, p + q = n).card

/-- LEAF. P0098 page 167, first sentence of the proof of Theorem 3.
External source: the almost all quantitative Goldbach theorem of Chudakov, Van der Corput
and Estermann, cited in Section 2. This source is not reproved in P0098. -/
theorem rich_density : ∃ γ : ℝ, 0 < γ ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ x : ℝ in atTop, (poorEven γ x : ℝ) ≤ δ * x := by
  sorry

/-- LEAF. P0098 page 167, the sampling proof with theta x equal to A log x.
The prime number theorem supplies the mean count and Chernoff bounds control failures.
This leaf includes the simultaneous eventual choice of a single prime set explicitly. -/
theorem thin_rich_approximation (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ (κ : ℝ) (P : Set ℕ), 0 < κ ∧ (∀ p ∈ P, Nat.Prime p) ∧
      ∀ᶠ x : ℝ in atTop,
        (count P x : ℝ) ≤ κ * Real.sqrt x ∧ (missedRich P γ x : ℝ) ≤ δ * x := by
  sorry

/-- LEAF. P0098 page 167, the expectation display splits failures into poor and rich integers.
The corresponding deterministic exception split is a finite set union bound. -/
theorem exception_split (P : Set ℕ) (γ x : ℝ) :
    badEven P x ≤ poorEven γ x + missedRich P γ x := by
  let R := Finset.range (⌊x⌋₊ + 1)
  let A := R.filter (fun n => Even n ∧ 2 < n ∧ n ∉ richEven γ)
  let B := R.filter (fun n => n ∈ richEven γ ∧ ¬ ∃ p ∈ P, ∃ q ∈ P, p + q = n)
  have hs : R.filter (fun n => Even n ∧ 2 < n ∧
      ¬ ∃ p ∈ P, ∃ q ∈ P, p + q = n) ⊆ A ∪ B := by
    intro n hn
    obtain ⟨hnR, he, hgt, hno⟩ := Finset.mem_filter.mp hn
    by_cases hr : n ∈ richEven γ
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hnR, hr, hno⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hnR, he, hgt, hr⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le A B)

/-- P0098 Theorem 3, page 163, assembled with exactly the cited proposition as its type.
CONDITIONAL ON rich_density and thin_rich_approximation. No sorry is used in this assembly. -/
theorem granville_theorem3_assembled : GranvilleTheorem3 := by
  intro ε hε
  obtain ⟨γ, hγ, hd⟩ := rich_density
  obtain ⟨κ, P, hκ, hP, hs⟩ := thin_rich_approximation γ (ε / 2) hγ (by positivity)
  refine ⟨κ, P, hκ, hP, ?_⟩
  filter_upwards [hd (ε / 2) (by positivity), hs] with x hx hxs
  refine ⟨hxs.1, ?_⟩
  have hc : (badEven P x : ℝ) ≤ (poorEven γ x : ℝ) + missedRich P γ x := by
    exact_mod_cast exception_split P γ x
  linarith [hxs.2]

end LeanLab.GoldbachAverage.Decomp124b
