/-
PP1993 pages 46 to 48, displays 14 to 26.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Full symmetric rational envelopes bound the Farey arcs used by the paper.
The geometry and analytic reductions are distinct OPEN leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RationalGlue489

namespace LeanLab.Languasco2004.Decomp489b
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp413b Decomp489a Decomp489f
noncomputable section

/-- LEAF. Page 46 display 14 and page 47 display 15, geometric reduction.
Each local window meets at most two Farey arcs. The full symmetric envelope
only increases each nonnegative mass. The factor four also includes the
square of the principal plus remainder decomposition. -/
theorem farey_local_reduction :
    ∃ N₀ : ℝ, ∀ N Y H B P R : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
      0 ≤ P → 0 ≤ R →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H → principalArcMass N Y H B q ≤ P) →
      (∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H →
        1 ≤ a → a ≤ q → Nat.Coprime a q → remainderArcMass N Y H B q a ≤ R) →
      ∀ ξ : ℝ, localMass N Y H B ξ ≤ 4 * (P + R) := by
  exact RationalGlue489.local_reduction_from_cover

/-- LEAF. Page 47 following display 15: only the principal rational term.
This is an elementary geometric sum tail estimate, separate from characters. -/
theorem principal_arc_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
      principalArcMass N (localization N η) (windowLength N η) (arcExponent η A) q ≤
        C * localization N η / Real.log N ^ (2 * A + 3) := by sorry

/-- LEAF. Page 47 displays 17 to 20: discard the bad characters using their
large modulus, their density and Parseval. The good character energy is
retained as a variable V, without estimating it. CONDITIONAL ON the two inputs. -/
theorem remainder_to_good
    (hzero : CharacterZeroFreeRegion) (hdensity : FixedModulusDensity) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ V : ℝ, 0 ≤ V →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        goodEnergy q N (localization N η) (windowLength N η) (arcExponent η A) ≤ V) →
      ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        1 ≤ a → a ≤ q → Nat.Coprime a q →
        remainderArcMass N (localization N η) (windowLength N η) (arcExponent η A) q a ≤
          C * (V + localization N η / Real.log N ^ (2 * A + 3)) := by sorry

/-- LEAF. Pages 47 and 48 displays 21 to 26: the short character energy
reduction before the final logarithmic parameter choice. U bounds each
value of the last supremum in display 26. CONDITIONAL ON the cited inputs.
The explicit formula to zero sum step remains inside this leaf. The
variable window reduction is a separate input from display 24. -/
theorem good_character_envelope
    (hdensity : FixedModulusDensity) (hgallagher : CharacterGallagher)
    (hexplicit : CharacterExplicitFormula) (hdyadic : DyadicCharacterReduction) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ U : ℝ, 0 ≤ U →
      (∀ σ : ℝ, 1 / 2 ≤ σ →
        σ ≤ 1 - 2 * arcExponent η A * Real.log (Real.log N) / Real.log N →
        localization N η ^ (1 - η / 3 * (1 - σ)) ≤ U) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder (windowLength N η) →
        goodEnergy q N (localization N η) (windowLength N η) (arcExponent η A) ≤
          C * (Real.log N ^ (20 : ℕ) * U +
            localization N η / Real.log N ^ (2 * A + 3)) := by sorry

#print axioms fareyOrder
#print axioms puncturedEnvelope
#print axioms principalArcMass
#print axioms remainderArcMass
#print axioms goodCharacters
#print axioms goodEnergy
#print axioms farey_local_reduction
#print axioms principal_arc_bound
#print axioms remainder_to_good
#print axioms good_character_envelope
end
end LeanLab.Languasco2004.Decomp489b
