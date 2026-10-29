import LeanLab.Ricci1937.CCounts
import LeanLab.Ricci1937.CErrorAbsorption
import LeanLab.Ricci1937.CTau
import LeanLab.Ricci1937.SigmaBar
import LeanLab.Ricci1937.Decomp87

/-!
Ricci 1937, Theorem C part 2, pages 82 and 83.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.Ricci1937
open Finset Filter Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 83, last lower display, with the gap from 2.4. -/
theorem decompJ342_lower_sieve (P : Polynomial ℤ) (hP : CHyp P) (s : ℕ)
    (hs : P.natDegree + 1 ≤ s) (hs3 : s ≤ 3 * P.natDegree) :
    ∃ a A : ℝ, 0 < a ∧ ∀ᶠ ξ : ℕ in atTop,
      a * ξ / Real.log ξ - A * (ξ : ℝ) ^
        (1 - (0.0052 : ℝ) / ((P.natDegree : ℝ) + 1)) < c2SiftedCount P s ξ := by
  exact decomp87_lower_sieve P hP s hs hs3

/-- LEAF. Page 82, application of 3.2 before removing the power error. -/
theorem decompJ342_upper_sieve (P : Polynomial ℤ) (hP : CHyp P) (ω : ℝ)
    (hω : 0 < ω) (herror : ω * (2 + 2 * ricciTau 1 + 0.01) < 1) :
    ∃ a A κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ᶠ ξ : ℕ in atTop,
      (decomp87FixedRoughCount P ω ξ : ℝ) ≤
        a * ξ / Real.log ξ + A * (ξ : ℝ) ^ (1 - κ) := by
  exact decomp87_upper_sieve P hP ω hω herror

/-- LEAF. Page 82, monotonicity of the fixed prime threshold. -/
theorem decompJ342_fixed_mono (P : Polynomial ℤ) {α β : ℝ} {ξ : ℕ}
    (hξ : 1 ≤ ξ) (hαβ : α ≤ β) :
    decomp87FixedRoughCount P β ξ ≤ decomp87FixedRoughCount P α ξ := by
  exact decomp87_fixed_mono P hξ hαβ

/-- LEAF. Page 82, cutoff with eta equal to one half. -/
theorem decompJ342_cutoff (P : Polynomial ℤ) {ω : ℝ} (hω : 0 < ω) (ξ : ℕ) :
    roughValueCount P ω ξ ≤ Nat.floor ((ξ : ℝ) ^ ((1 : ℝ) / 2)) +
      decomp87FixedRoughCount P (ω / 2) ξ := by
  exact decomp87_cutoff P hω ξ

/-- LEAF. Page 82, a smaller exponent giving a saved power upper error. -/
theorem decompJ342_upper_parameter {ω : ℝ} (hω : 0 < ω) :
    0 < min (ω / 2) (1 / 8) ∧ min (ω / 2) (1 / 8) ≤ ω / 2 ∧
      min (ω / 2) (1 / 8) * (2 + 2 * ricciTau 1 + 0.01) < 1 := by
  exact decomp87_upper_parameter hω

/-- LEAF. Page 83, absorb the saved power lower remainder. -/
theorem decompJ342_lower_absorb (P : Polynomial ℤ) (s : ℕ) {a A : ℝ}
    (ha : 0 < a)
    (hbound : ∀ᶠ ξ : ℕ in atTop,
      a * ξ / Real.log ξ - A * (ξ : ℝ) ^
        (1 - (0.0052 : ℝ) / ((P.natDegree : ℝ) + 1)) < c2SiftedCount P s ξ) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      b * ξ / Real.log ξ < c2SiftedCount P s ξ := by
  exact decomp87_lower_absorb P s ha hbound

/-- LEAF. Page 82, absorb the cutoff and upper sieve power error. -/
theorem decompJ342_upper_absorb (P : Polynomial ℤ) {ω δ a A κ : ℝ}
    (hω : 0 < ω) (hδ : δ ≤ ω / 2) (ha : 0 < a) (hκ : 0 < κ)
    (hbound : ∀ᶠ ξ : ℕ in atTop,
      (decomp87FixedRoughCount P δ ξ : ℝ) ≤
        a * ξ / Real.log ξ + A * (ξ : ℝ) ^ (1 - κ)) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      (roughValueCount P ω ξ : ℝ) < b * ξ / Real.log ξ := by
  exact decomp87_upper_absorb P hω hδ ha hκ hbound

/-- LEAF. Page 83, elementary lower survivor inclusion from task67. -/
theorem decompJ342_lower_inclusion (P : Polynomial ℤ) (hP : CHyp P) {s ξ : ℕ}
    (hs : P.natDegree < s) (hξ : 1 ≤ ξ) :
    c2SiftedCount P s ξ ≤ c2ValueCount P s ξ := by
  exact decomp87_lower_inclusion P hP hs hξ

/-- LEAF. Page 83, elementary upper inclusion from task67. -/
theorem decompJ342_upper_inclusion (P : Polynomial ℤ) (s ξ : ℕ) :
    c2ValueCount P s ξ ≤ roughValueCount P (((s : ℝ) - P.natDegree) / (2 * s)) ξ := by
  exact decomp87_upper_inclusion P s ξ

/-- The final assembly matching exactly TheoremC2. -/
theorem ricciC2_decompJ342 : TheoremC2 := by
  intro P hP s hs h3s
  obtain ⟨a, A, ha, hraw⟩ := decompJ342_lower_sieve P hP s hs h3s
  obtain ⟨b, hb, N₁, hlower⟩ := decompJ342_lower_absorb P s ha hraw
  let ω : ℝ := ((s : ℝ) - P.natDegree) / (2 * s)
  have hsR : (P.natDegree : ℝ) < s := by exact_mod_cast (by omega : P.natDegree < s)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by have := hP.1; omega : 0 < s)
  have hω : 0 < ω := by dsimp [ω]; positivity
  obtain ⟨hδpos, hδle, hδerror⟩ := decompJ342_upper_parameter hω
  obtain ⟨c, B, κ, hc, hκ, hrawupper⟩ :=
    decompJ342_upper_sieve P hP (min (ω / 2) (1 / 8)) hδpos hδerror
  obtain ⟨d, hd, N₂, hupper⟩ := decompJ342_upper_absorb P hω hδle hc hκ hrawupper
  refine ⟨b, d, hb, hd, max N₁ N₂, fun ξ hξ => ?_⟩
  change b * ξ / Real.log ξ < (c2ValueCount P s ξ : ℝ) ∧ (c2ValueCount P s ξ : ℝ) < d * ξ / Real.log ξ
  constructor
  · apply lt_of_lt_of_le (hlower ξ (by omega))
    exact_mod_cast (show c2SiftedCount P s ξ ≤ c2ValueCount P s ξ from c2SiftedCount_le P hP (by omega : P.natDegree < s) (by omega : 1 ≤ ξ))
  · apply lt_of_le_of_lt _ (hupper ξ (by omega))
    exact_mod_cast (show c2ValueCount P s ξ ≤ roughValueCount P ω ξ from c2ValueCount_le_rough P s ξ)

end
end LeanLab.Ricci1937
