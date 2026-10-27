import LeanLab.Ricci1937.CSurvivors
import LeanLab.Ricci1937.CPolynomialBounds
import LeanLab.Ricci1937.CImplications

/-!
Ricci 1937, pages 82 and 83. Explicit count comparisons and unresolved sieve inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The count in Theorem C part 2. -/
def c2ValueCount (P : Polynomial ℤ) (s ξ : ℕ) : ℕ :=
  #{n ∈ Icc (1 : ℕ) ξ | AlmostGT ((2 * s * P.natDegree - 1) / (s - P.natDegree))
      (((n : ℕ) : ℝ) ^ (((s : ℝ) - P.natDegree) / (2 * s))) (Fval P n) ∧
      ∀ p ∈ (Fval P n).primeFactors, (Fval P n).factorization p < s}

/-- The positive values with all factors above the variable power threshold of page 82. -/
def roughValueCount (P : Polynomial ℤ) (ω : ℝ) (ξ : ℕ) : ℕ :=
  #{n ∈ Icc (1 : ℕ) ξ | 1 ≤ Fval P n ∧
      ∀ p ∈ (Fval P n).primeFactorsList, (((n : ℕ) : ℝ) ^ ω) < (p : ℝ)}

/-- Page 83 survivors with the explicit larger coefficient bound from CPolynomialBounds. -/
def c2SiftedCount (P : Polynomial ℤ) (s ξ : ℕ) : ℕ :=
  #{n ∈ Icc (1 : ℕ) ξ | 1 ≤ Fval P n ∧
      (∀ p ∈ (Fval P n).primeFactorsList,
        (valueCoeffBound P : ℝ) * (ξ : ℝ) ^ (((s : ℝ) - P.natDegree) / (2 * s)) < (p : ℝ)) ∧
      ∀ p : ℕ, p.Prime → p ^ 2 ∣ Fval P n →
        (valueCoeffBound P : ℝ) * (ξ : ℝ) ^ ((P.natDegree : ℝ) / s) < (p : ℝ)}

/-- Page 83: every positive sieve survivor is counted by C2. -/
theorem c2SiftedCount_le (P : Polynomial ℤ) (hP : CHyp P) {s ξ : ℕ}
    (hsg : P.natDegree < s) (hξ : 1 ≤ ξ) :
    c2SiftedCount P s ξ ≤ c2ValueCount P s ξ := by
  apply card_le_card
  intro n hn
  rcases mem_filter.mp hn with ⟨hnI, hx, hrough, hsquare⟩
  have hnξ := (mem_Icc.mp hnI).2
  apply mem_filter.mpr
  refine ⟨hnI, ?_⟩
  apply c2_survivor hP.1 hsg hx
    (C := (valueCoeffBound P : ℝ)) (ξ := (ξ : ℝ))
  · exact_mod_cast (show 1 ≤ valueCoeffBound P by unfold valueCoeffBound; omega)
  · exact_mod_cast hξ
  · exact_mod_cast hnξ
  · exact_mod_cast Fval_lt_valueCoeffBound P hξ hnξ
  · exact hrough
  · exact hsquare

/-- Page 83: dropping the factor count and multiplicity conditions gives the page 82 count. -/
theorem c2ValueCount_le_rough (P : Polynomial ℤ) (s ξ : ℕ) :
    c2ValueCount P s ξ ≤ roughValueCount P (((s : ℝ) - P.natDegree) / (2 * s)) ξ := by
  apply card_le_card
  intro n hn
  rcases mem_filter.mp hn with ⟨hnI, hx, _⟩
  exact mem_filter.mpr ⟨hnI, hx.1, hx.2.2⟩

/-- Unresolved lower sieve count target for the page 83 thresholds.
This is a consequence sought from Theorem I, not an established theorem. -/
def C2LowerSieveInput : Prop :=
  ∀ P : Polynomial ℤ, CHyp P → ∀ s : ℕ, P.natDegree + 1 ≤ s → s ≤ 3 * P.natDegree →
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      a * ξ / Real.log ξ < c2SiftedCount P s ξ

/-- Unresolved upper sieve count target from the first theorem on page 82. -/
def RoughUpperSieveInput : Prop :=
  ∀ P : Polynomial ℤ, CHyp P → ∀ ω : ℝ, 0 < ω →
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ ξ : ℕ, N < ξ →
      (roughValueCount P ω ξ : ℝ) < a * ξ / Real.log ξ

/-- CONDITIONAL ON the named lower and upper sieve count inputs. -/
theorem theoremC2_of_sieveCounts (hlower : C2LowerSieveInput)
    (hupper : RoughUpperSieveInput) : TheoremC2 := by
  intro P hP s hs h3s
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by have := hP.1; omega : 0 < s)
  have hsgR : (P.natDegree : ℝ) < s := by exact_mod_cast (by omega : P.natDegree < s)
  obtain ⟨a₁, ha₁, N₁, h₁⟩ := hlower P hP s hs h3s
  obtain ⟨a₂, ha₂, N₂, h₂⟩ :=
    hupper P hP (((s : ℝ) - P.natDegree) / (2 * s)) (by positivity)
  refine ⟨a₁, a₂, ha₁, ha₂, max N₁ N₂, fun ξ hξ => ?_⟩
  change a₁ * ξ / Real.log ξ < (c2ValueCount P s ξ : ℝ) ∧
    (c2ValueCount P s ξ : ℝ) < a₂ * ξ / Real.log ξ
  constructor
  · apply lt_of_lt_of_le (h₁ ξ (by omega))
    exact_mod_cast c2SiftedCount_le P hP (by omega : P.natDegree < s) (by omega : 1 ≤ ξ)
  · apply lt_of_le_of_lt _ (h₂ ξ (by omega))
    exact_mod_cast c2ValueCount_le_rough P s ξ

/-- CONDITIONAL ON the same two count inputs. Page 83 gives C1 from C2. -/
theorem theoremC1_of_sieveCounts (hlower : C2LowerSieveInput)
    (hupper : RoughUpperSieveInput) : TheoremC1 :=
  theoremC1_of_C2 (theoremC2_of_sieveCounts hlower hupper)

example : c2SiftedCount (Polynomial.X : Polynomial ℤ) 3 27 ≤
    c2ValueCount (Polynomial.X : Polynomial ℤ) 3 27 := by
  apply c2SiftedCount_le
  · exact ⟨by simp, Polynomial.monic_X.isPrimitive, Polynomial.irreducible_X, by simp⟩
  · norm_num
  · norm_num

example : c2ValueCount (Polynomial.X : Polynomial ℤ) 3 27 ≤
    roughValueCount (Polynomial.X : Polynomial ℤ) ((1 : ℝ) / 3) 27 := by
  convert c2ValueCount_le_rough (Polynomial.X : Polynomial ℤ) 3 27 using 1
  norm_num

end
end LeanLab.Ricci1937
