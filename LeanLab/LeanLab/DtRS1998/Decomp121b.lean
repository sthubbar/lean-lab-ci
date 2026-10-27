/-
AI wrote this Lean code for CODEX task121.
P0037 Theorem 2, printed page 206, and Sections 5.1 and 5.2, pages 211 to 214.
This is a decomposition of the existing cited FullTheorem2 statement.
The twelve old interval proofs are reused. No range is extended.
The remaining computational leaves stay cited. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper
import LeanLab.DtRS1998.Interval15
import LeanLab.DtRS1998.Interval20
import LeanLab.DtRS1998.Interval25
import LeanLab.DtRS1998.Interval30
import LeanLab.DtRS1998.Interval35
import LeanLab.DtRS1998.Interval40
import LeanLab.DtRS1998.Interval45
import LeanLab.DtRS1998.Interval50
import LeanLab.DtRS1998.Interval55
import LeanLab.DtRS1998.Interval60
import LeanLab.DtRS1998.Interval65
import LeanLab.DtRS1998.Interval70

namespace LeanLab.DtRS1998.Decomp121b

open LeanLab Task71.Paper

/-- LEAF. P0037 Theorem 2 page 206 and Section 5.1 page 211.
The first twelve intervals are already proved in the lab. -/
theorem first_family_proved :
    ∀ i : ℕ, 3 ≤ i → i ≤ 14 → IntervalSum (10 ^ (5 * i)) (10 ^ 8) := by
  intro i hlo hhi
  interval_cases i
  · exact theorem2_i3
  · exact I20.theorem2
  · exact I25.theorem2
  · exact I30.theorem2
  · exact I35.theorem2
  · exact I40.theorem2
  · exact I45.theorem2
  · exact I50.theorem2
  · exact I55.theorem2
  · exact I60.theorem2
  · exact I65.theorem2
  · exact I70.theorem2


/-- LEAF. P0037 Theorem 2 page 206 and Section 5.1 pages 211 to 213.
The six intervals beyond the existing kernel verification are cited computations. -/
theorem first_family_remaining :
    ∀ i : ℕ, 15 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8) := by
  sorry

/-- LEAF. P0037 Theorem 2 page 206 and Section 5.2 pages 212 to 214.
The eleven intervals at powers 200 through 300 are cited computations. -/
theorem second_family :
    ∀ i : ℕ, 20 ≤ i → i ≤ 30 → IntervalSum (10 ^ (10 * i)) (10 ^ 9) := by
  sorry

/-- CONDITIONAL ON the supplied remaining first family and second family.
P0037 Theorem 2 page 206. This assembly uses no cited sorry leaf. -/
theorem theorem2_of_remaining
    (hfirst : ∀ i : ℕ, 15 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8))
    (hsecond : ∀ i : ℕ, 20 ≤ i → i ≤ 30 → IntervalSum (10 ^ (10 * i)) (10 ^ 9)) :
    FullTheorem2 := by
  constructor
  · intro i hlo hhi
    by_cases hi : i ≤ 14
    · exact first_family_proved i hlo hi
    · exact hfirst i (by omega) hhi
  · exact hsecond

/-- CONDITIONAL ON the two unproved computational leaves.
The target is exactly the cited FullTheorem2 already present on main. -/
theorem theorem2 : FullTheorem2 :=
  theorem2_of_remaining first_family_remaining second_family

#print axioms first_family_proved
#print axioms first_family_remaining
#print axioms second_family
#print axioms theorem2_of_remaining
#print axioms theorem2

end LeanLab.DtRS1998.Decomp121b
