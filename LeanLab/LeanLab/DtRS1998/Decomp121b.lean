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
import LeanLab.DtRS1998.Decomp270a
import LeanLab.DtRS1998.Certificate294
import LeanLab.DtRS1998.Decomp372a
import LeanLab.DtRS1998.Decomp372b
import LeanLab.DtRS1998.Decomp372c
import LeanLab.DtRS1998.Candidate445
import LeanLab.DtRS1998.Decomp121bSecond

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


/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^75, and the page 207 recurrence for the sets F: the listed
primes q near 10^75 cover every even n in the interval by n - q prime.
Reuses the proved certificate Task294 row 75 through Decomp270a. -/
theorem interval_75 : IntervalSum (10 ^ 75) (10 ^ 8) := by
  obtain ⟨qs, _, hq, hc⟩ := Decomp270a.certificate75
  exact Decomp270a.interval_of_certificate (by decide) (fun q h => (hq q h).1) hc

/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^80, and the page 207 recurrence for the sets F: the listed
primes q near 10^80 cover every even n in the interval by n - q prime.
Reuses the proved certificate Task294 row 80 through Decomp270a. -/
theorem interval_80 : IntervalSum (10 ^ 80) (10 ^ 8) := by
  obtain ⟨qs, _, hq, hc⟩ := Decomp270a.certificate80
  exact Decomp270a.interval_of_certificate (by decide) (fun q h => (hq q h).1) hc

/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^85, and the page 207 recurrence for the sets F: the listed
primes q near 10^85 cover every even n in the interval by n - q prime.
Reuses the proved certificate Task294 row 85 through Decomp270a. -/
theorem interval_85 : IntervalSum (10 ^ 85) (10 ^ 8) := by
  obtain ⟨qs, _, hq, hc⟩ := Decomp270a.certificate85
  exact Decomp270a.interval_of_certificate (by decide) (fun q h => (hq q h).1) hc

/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^90, and the page 207 recurrence for the sets F.
CONDITIONAL ON the candidate primality leaves of Candidate445.T90, as in
Decomp445d.certificate90; the window coverage of Decomp372a is reused. -/
theorem interval_90 : IntervalSum (10 ^ 90) (10 ^ 8) := by
  have hcheck := Certificate294.offsets_certificate (B := 10 ^ 90) (L := 10 ^ 8)
    (fun d hd => le_trans (Decomp372a.offset_bounds d hd) (by norm_num)) Decomp372a.offset_cover
  exact Decomp270a.interval_of_certificate (by decide) Candidate445.T90.candidate_primes hcheck

/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^95, and the page 207 recurrence for the sets F.
CONDITIONAL ON the candidate primality leaves of Candidate445.T95, as in
Decomp445d.certificate95; the window coverage of Decomp372b is reused. -/
theorem interval_95 : IntervalSum (10 ^ 95) (10 ^ 8) := by
  have hcheck := Certificate294.offsets_certificate (B := 10 ^ 95) (L := 10 ^ 8)
    (fun d hd => le_trans (Decomp372b.offset_bounds d hd) (by norm_num)) Decomp372b.offset_cover
  exact Decomp270a.interval_of_certificate (by decide) Candidate445.T95.candidate_primes hcheck

/-- Split of first_family_remaining, burst 20261112. AI wrote this Lean code.
P0037 Section 5.1 page 211, the unnumbered interval display, with Table 1
page 213, row 10^100, and the page 207 recurrence for the sets F.
CONDITIONAL ON the candidate primality leaves of Candidate445.T100, as in
Decomp445d.certificate100; the window coverage of Decomp372c is reused. -/
theorem interval_100 : IntervalSum (10 ^ 100) (10 ^ 8) := by
  have hcheck := Certificate294.offsets_certificate (B := 10 ^ 100) (L := 10 ^ 8)
    (fun d hd => le_trans (Decomp372c.offset_bounds d hd) (by norm_num)) Decomp372c.offset_cover
  exact Decomp270a.interval_of_certificate (by decide) Candidate445.T100.candidate_primes hcheck

/-- P0037 Theorem 2 page 206 and Section 5.1 pages 211 to 213.
Split in burst 20261112: assembled from the six row lemmas interval_75
through interval_100 above, one per row of Table 1 page 213. No sorry of its own. -/
theorem first_family_remaining :
    ∀ i : ℕ, 15 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8) := by
  intro i hlo hhi
  interval_cases i
  · exact interval_75
  · exact interval_80
  · exact interval_85
  · exact interval_90
  · exact interval_95
  · exact interval_100

/-- P0037 Theorem 2 page 206 and Section 5.2 pages 212 to 214.
The eleven intervals at powers 200 through 300 are cited computations.
Split in the route burst of 2026-11-12: CONDITIONAL ON the two open Table 2
certificate lemmas in Decomp121bSecond; this proof has no sorry of its own. -/
theorem second_family :
    ∀ i : ℕ, 20 ≤ i → i ≤ 30 → IntervalSum (10 ^ (10 * i)) (10 ^ 9) := by
  intro i hlo hhi
  have hcert : ∃ qs : List ℕ, qs.length ≤ 231 ∧ (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ (10 * i) + 2 * j ∧ (10 ^ (10 * i) + 2 * j - q).Prime))) = true := by
    by_cases hlow : i ≤ 25
    · exact Decomp121bSecond.table2_certificates_lower i hlo hlow
    · exact Decomp121bSecond.table2_certificates_upper i (by omega) hhi
  obtain ⟨qs, _, hq, hc⟩ := hcert
  exact Decomp121bSecond.interval_of_table2_certificate
    (Decomp121bSecond.table2_base_even i (by omega)) hq hc

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
#print axioms interval_75
#print axioms interval_80
#print axioms interval_85
#print axioms interval_90
#print axioms interval_95
#print axioms interval_100
#print axioms first_family_remaining
#print axioms second_family
#print axioms theorem2_of_remaining
#print axioms theorem2

end LeanLab.DtRS1998.Decomp121b
