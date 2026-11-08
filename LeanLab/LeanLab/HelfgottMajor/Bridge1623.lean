import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.Decomp389c
import LeanLab.HelfgottMajor.DecompJ1233
import LeanLab.DERZ1997.Decomp1529a

/-!
Bridges from the shared zero count of U-1623 to the older copies. Unit U-1623.
Each theorem repeats the statement of one older leaf word for word
and proves it from ZeroCount1623.book_zero_count alone, so it never calls the older sorry.
The older files stay sealed. The main thread reroutes them through these REPAIR lines.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Bridge1623
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389a Decomp389c ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- The summability half of the Decomp389a leaf. No hypothesis on chi or T is needed. -/
theorem veryLowCountTerm_summable (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (veryLowCountTerm χ T) :=
  summable_zeroIdx χ T _

/-- The summability half of the Decomp389c leaf. No hypothesis on chi or T is needed. -/
theorem stripCountTerm_summable (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Summable (stripCountTerm χ T) :=
  summable_zeroIdx χ T _

/-- Word for word Decomp389a.very_low_zero_count, page 39 of the arXiv version.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem very_low_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 :=
  ⟨veryLowCountTerm_summable χ T, ZeroCount1623.very_low_count χ hχ T hT⟩

/-- Word for word DecompJ1233.leaf_very_low_zero_count, page 39 of the arXiv version.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem leaf_very_low_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (veryLowCountTerm χ T) ∧
      (∑' ρ, veryLowCountTerm χ T ρ) ≤ 0.819 * log q + 16.8 :=
  very_low_zero_count q χ hχ T hT

/-- Word for word Decomp389c.strip_zero_count, arXiv pages 37 and 38, displays 4.25 and 4.26.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem strip_zero_count (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (T : ℝ) (hT : 1 ≤ T) :
    Summable (stripCountTerm χ T) ∧
      (∑' ρ, stripCountTerm χ T ρ) ≤
        T / π * log ((q : ℝ) * T / (2 * π * exp 1)) +
          0.5 * log ((q : ℝ) * T) + 17.7 :=
  ⟨stripCountTerm_summable χ T, ZeroCount1623.strip_count χ hχ T hT⟩

/-- Word for word DERZ1997.Decomp1529a.primitive_zero_count193, arXiv pages 37 and 38.
The finiteness hypothesis is kept to match the leaf, and the two finite sums agree.
CONDITIONAL ON ZeroCount1623.book_zero_count. -/
theorem primitive_zero_count193 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LeanLab.DERZ1997.Decomp1529a.LZeros χ T).Finite) :
    |(∑ ρ ∈ hfin.toFinset, (LeanLab.DERZ1997.Decomp1529a.LMult χ ρ : ℝ)) -
      T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log (q * T) + 17.7 :=
  ZeroCount1623.arxiv_zero_count χ hχ hT

/-- Word for word Decomp269b.very_low_mass_bound and its two later copies, page 39.
CONDITIONAL ON ZeroCount1623.book_zero_count. The Mellin bound is the proved DecompJ1233 one. -/
theorem very_low_mass_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    veryLowMass χ δ T ≤ 2.15581 * (0.819 * log q + 16.8) := by
  obtain ⟨hcount, hbudget⟩ := very_low_zero_count q χ hχ T hT
  exact (very_low_mass_le_count χ δ T hzeros hcount
    (fun s hs => DecompJ1233.leaf_mellin_critical_norm_le δ s hs)).trans
      (mul_le_mul_of_nonneg_left hbudget (by norm_num))

/-- Claim 4, summability. The middle mass family is summable with no assumption at all,
because the index set is finite, so the real tsum in middleMass never defaults to zero.
Proved unconditionally. Decomp269b page 40. -/
theorem middle_family_summable (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ (fun ρ => mellinMassTerm χ δ ρ.val) ρ) :=
  summable_zeroIdx χ T _

/-- Claim 4, summability of the very low family. Proved unconditionally. -/
theorem very_low_family_summable (χ : DirichletCharacter ℂ q) (δ T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} =>
        Set.indicator {ρ | |ρ.val.im| ≤ 1} (fun ρ => mellinMassTerm χ δ ρ.val) ρ) :=
  summable_zeroIdx χ T _

/-- Vacuity instance for the bridges, the modulus 1 character at height 1. -/
example : (1 : DirichletCharacter ℂ 1).IsPrimitive :=
  DirichletCharacter.isPrimitive_one_level_one

end LeanLab.HelfgottMajor.Bridge1623

#print axioms LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.LFunction_inv_conj
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.mult_inv_conj
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.bookCount_inv
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.zero_count_two_sided
#print axioms LeanLab.HelfgottMajor.ZeroCount1623.arxiv_zero_count
#print axioms LeanLab.HelfgottMajor.Bridge1623.veryLowCountTerm_summable
#print axioms LeanLab.HelfgottMajor.Bridge1623.stripCountTerm_summable
#print axioms LeanLab.HelfgottMajor.Bridge1623.middle_family_summable
#print axioms LeanLab.HelfgottMajor.Bridge1623.very_low_family_summable
#print axioms LeanLab.HelfgottMajor.Bridge1623.very_low_zero_count
#print axioms LeanLab.HelfgottMajor.Bridge1623.leaf_very_low_zero_count
#print axioms LeanLab.HelfgottMajor.Bridge1623.strip_zero_count
#print axioms LeanLab.HelfgottMajor.Bridge1623.primitive_zero_count193
#print axioms LeanLab.HelfgottMajor.Bridge1623.very_low_mass_bound
