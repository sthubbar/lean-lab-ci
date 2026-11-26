import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C0
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C1
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C2
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C3
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C4
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C5
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C6
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C7
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C8
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C9
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C10
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C11
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C12
import LeanLab.OpenProblems.Feed1122Novelty1615StackS142C13

/-!
# Erdős 273, Novelty1615, S142: assembly of the high block split

AI wrote this Lean code. Erdős 273 is OPEN and so is binary Goldbach. The 67 orbit candidates are
ruled out sorry free, conditional on `Feed1122Split.leaf_recip_classification`; the other 353
candidates of the high block stay a LEAF of the cited residue search.
-/

namespace LeanLab.OpenProblems.Novelty1615.Feed1122StackS142

open LeanLab.OpenProblems.Erdos273 LeanLab.OpenProblems.Novelty1615
open LeanLab.OpenProblems.Novelty1615.Feed1122Split

/-- The full orbit certificate table, 67 candidates in `[4000000, 8000000)`. -/
def certs : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ))) :=
  certs0 ++ certs1 ++ certs2 ++ certs3 ++ certs4 ++ certs5 ++ certs6 ++ certs7 ++ certs8 ++ certs9 ++ certs10 ++ certs11 ++ certs12 ++ certs13

theorem certOK_append (l₁ l₂ : List (ℕ × List (ℕ × ℕ) × List (ℕ × List (ℕ × ℕ)))) :
    certOK (l₁ ++ l₂) = (certOK l₁ && certOK l₂) := List.all_append

theorem certOK_true : certOK certs = true := by
  simp only [certs, certOK_append, certOK0, certOK1, certOK2, certOK3, certOK4, certOK5, certOK6, certOK7, certOK8, certOK9, certOK10, certOK11, certOK12, certOK13, Bool.and_self]

/-- The 67 orbit candidates: no admissible covering has its lcm among them. Proved, conditional on
`leaf_recip_classification`. -/
theorem no_cover_orbit :
    ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∈ certs.map Prod.fst →
        False :=
  certOK_sound certs certOK_true

/-- LEAF: residue search step of the cited search, https://github.com/veljjanoski/erdos273,
restricted to the 353 candidates of the high block that the orbit chains do not reach: no covering
with distinct moduli `p - 1`, `p ≥ 5` prime, has its lcm in `badList`, at least `4000000`, and
outside the orbit table `certs`. Implied by the cited claim, no stronger than it. Class HARD: an
exhaustive residue assignment search per candidate. -/
theorem leaf_no_cover_bad_high_rest :
    ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∈ badList →
        4000000 ≤ S.lcm Prod.fst → S.lcm Prod.fst ∉ certs.map Prod.fst → False := by
  sorry

/-- Assembly, sorry free from the pieces: the identical statement of
`Feed1122Stack.leaf_no_cover_bad_high`. -/
theorem leaf_no_cover_bad_high_proved :
    ∀ S : Finset (ℕ × ℤ), Covers S → Set.InjOn Prod.fst (S : Set (ℕ × ℤ)) →
      (∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) → S.lcm Prod.fst ∈ badList →
        4000000 ≤ S.lcm Prod.fst → False := by
  intro S hS hi hp hb h4
  by_cases hc : S.lcm Prod.fst ∈ certs.map Prod.fst
  · exact no_cover_orbit S hS hi hp hc
  · exact leaf_no_cover_bad_high_rest S hS hi hp hb h4 hc

end LeanLab.OpenProblems.Novelty1615.Feed1122StackS142
