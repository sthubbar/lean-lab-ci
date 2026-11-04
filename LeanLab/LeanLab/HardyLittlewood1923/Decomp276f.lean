/-
AI wrote this Lean code for CODEX task276.
P0004 pages 64 and 65, the finite residue argument in equation 5.6913.
These are finite pattern maxima, not an identification with the prime window limsup.
The latter identification requires the paper's Hypothesis X.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.Decomp276d

namespace LeanLab.HardyLittlewood1923.Decomp276f

open Finset
open LeanLab.HardyLittlewood1923.Section5
open LeanLab.HardyLittlewood1923.Decomp276d

/-- P0004 page 64 possible groups, represented by offsets in an interval of length x. -/
noncomputable def admissiblePatterns (x : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((range x).powerset).filter Possible

/-- P0004 pages 64 and 65, the finite residue test with prime cutoff mu. -/
noncomputable def boundedPatterns (x μ : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((range x).powerset).filter fun b =>
    ∀ q ∈ Nat.primesLE μ, ∃ a < q, ∀ y ∈ b, y % q ≠ a

/-- The largest cardinality of an admissible offset pattern of length at most x.
P0004 page 64, the finite pattern counterpart of rho. -/
noncomputable def admissibleMax (x : ℕ) : ℕ := (admissiblePatterns x).sup card

/-- The largest cardinality passing the finite prime test with cutoff mu.
P0004 page 65 equation 5.6913, the finite pattern counterpart of the truncated maximum. -/
noncomputable def boundedMax (x μ : ℕ) : ℕ := (boundedPatterns x μ).sup card

/-- P0004 page 64, the elementary interval length bound for a pattern maximum. -/
theorem boundedMax_le_length (x μ : ℕ) : boundedMax x μ ≤ x := by
  classical
  apply Finset.sup_le
  intro b hb
  have hsub : b ⊆ range x := mem_powerset.mp (mem_filter.mp hb).1
  simpa only [card_range] using card_le_card hsub

/-- P0004 page 64 equation 5.6911, admissible patterns pass every finite prime test. -/
theorem admissibleMax_le_boundedMax (x μ : ℕ) : admissibleMax x ≤ boundedMax x μ := by
  classical
  apply Finset.sup_le
  intro b hb
  obtain ⟨hsub, hpos⟩ := mem_filter.mp hb
  apply Finset.le_sup
  exact mem_filter.mpr ⟨hsub, fun q hq => hpos q (Nat.prime_of_mem_primesLE hq)⟩

/-- P0004 page 65 equation 5.6913, finite pattern stability.
If the truncated maximum is at most its prime cutoff, every maximizing pattern is admissible. -/
theorem boundedMax_stable {x μ : ℕ} (h : boundedMax x μ ≤ μ) :
    boundedMax x μ = admissibleMax x := by
  classical
  apply le_antisymm ?_ (admissibleMax_le_boundedMax x μ)
  apply Finset.sup_le
  intro b hb
  have hc : b.card ≤ μ := (show b.card ≤ boundedMax x μ from Finset.le_sup hb).trans h
  obtain ⟨hsub, hsmall⟩ := mem_filter.mp hb
  have hp : Possible b := possible_of_small_primes b (fun q hq hqb =>
    hsmall q (Nat.mem_primesLE.mpr ⟨hqb.trans hc, hq⟩))
  exact Finset.le_sup (mem_filter.mpr ⟨hsub, hp⟩)

/-- P0004 page 64 equation 5.6911, increasing the cutoff can only decrease the finite maximum. -/
theorem boundedMax_antitone_cutoff (x : ℕ) {μ ν : ℕ} (hμν : μ ≤ ν) :
    boundedMax x ν ≤ boundedMax x μ := by
  classical
  apply Finset.sup_le
  intro b hb
  obtain ⟨hsub, hsmall⟩ := mem_filter.mp hb
  apply Finset.le_sup
  refine mem_filter.mpr ⟨hsub, fun q hq => ?_⟩
  exact hsmall q (Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hq).trans hμν, Nat.prime_of_mem_primesLE hq⟩)

/-- P0004 page 65, the full interval length is a sufficient prime cutoff for the finite maximum. -/
theorem boundedMax_full (x : ℕ) : boundedMax x x = admissibleMax x := by
  exact boundedMax_stable (boundedMax_le_length x x)

/-- P0004 pages 64 and 65. A concrete nonempty instance of the finite pattern maximum. -/
theorem admissibleMax_one : admissibleMax 1 = 1 := by
  classical
  have hu : admissibleMax 1 ≤ 1 :=
    (admissibleMax_le_boundedMax 1 1).trans (boundedMax_le_length 1 1)
  have hm : ({0} : Finset ℕ) ∈ admissiblePatterns 1 :=
    mem_filter.mpr ⟨mem_powerset.mpr (by simp), singleton_possible⟩
  have hl : 1 ≤ admissibleMax 1 := by
    simpa only [card_singleton, admissibleMax] using (Finset.le_sup (f := card) hm)
  omega

#print axioms boundedMax_le_length
#print axioms admissibleMax_le_boundedMax
#print axioms boundedMax_stable
#print axioms boundedMax_antitone_cutoff
#print axioms boundedMax_full
#print axioms admissibleMax_one

end LeanLab.HardyLittlewood1923.Decomp276f
