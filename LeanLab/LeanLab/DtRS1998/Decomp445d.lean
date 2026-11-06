/-
AI wrote this Lean code for CODEX task445.
P0037 Theorem 2 page 206 and Sections 5.1 and 5.2 pages 211 to 214.
Use the twelve new primary components through the candidate list bridges.
The nine later prime batches and eleven Table 2 certificates stay OPEN.
The final exact assembly uses only the supplied leaves.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Candidate445
import LeanLab.DtRS1998.Decomp372d

namespace LeanLab.DtRS1998.Decomp445d

open Task71.Paper Decomp270a Certificate294

/-- P0037 page 211 and Table 1 page 213, row 10^90.
CONDITIONAL ON four new primary components and three older prime batches.
The finite small-complement coverage and candidate bounds are reused.
This is the exact Decomp270a.certificate90 statement. -/
theorem certificate90 :
    ∃ qs : List ℕ, qs.length ≤ 209 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 90 - 65981 ≤ q ∧ q ≤ 10 ^ 90) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 90 + 2 * j ∧ (10 ^ 90 + 2 * j - q).Prime))) = true := by
  refine ⟨Decomp372a.qs, by rw [Decomp372a.length_eq], ?_, ?_⟩
  · intro q hq
    exact ⟨Candidate445.T90.candidate_primes q hq, Decomp372a.bounds q hq⟩
  · exact offsets_certificate
      (fun d hd => le_trans (Decomp372a.offset_bounds d hd) (by norm_num)) Decomp372a.offset_cover


/-- P0037 page 211 and Table 1 page 213, row 10^95.
CONDITIONAL ON four new primary components and three older prime batches.
The finite small-complement coverage and candidate bounds are reused.
This is the exact Decomp270a.certificate95 statement. -/
theorem certificate95 :
    ∃ qs : List ℕ, qs.length ≤ 207 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 95 - 64011 ≤ q ∧ q ≤ 10 ^ 95) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 95 + 2 * j ∧ (10 ^ 95 + 2 * j - q).Prime))) = true := by
  refine ⟨Decomp372b.qs, by rw [Decomp372b.length_eq], ?_, ?_⟩
  · intro q hq
    exact ⟨Candidate445.T95.candidate_primes q hq, Decomp372b.bounds q hq⟩
  · exact offsets_certificate
      (fun d hd => le_trans (Decomp372b.offset_bounds d hd) (by norm_num)) Decomp372b.offset_cover


/-- P0037 page 211 and Table 1 page 213, row 10^100.
CONDITIONAL ON four new primary components and three older prime batches.
The finite small-complement coverage and candidate bounds are reused.
This is the exact Decomp270a.certificate100 statement. -/
theorem certificate100 :
    ∃ qs : List ℕ, qs.length ≤ 250 ∧
      (∀ q ∈ qs, q.Prime ∧ 10 ^ 100 - 68969 ≤ q ∧ q ≤ 10 ^ 100) ∧
      (List.range (10 ^ 8 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 100 + 2 * j ∧ (10 ^ 100 + 2 * j - q).Prime))) = true := by
  refine ⟨Decomp372c.qs, by rw [Decomp372c.length_eq], ?_, ?_⟩
  · intro q hq
    exact ⟨Candidate445.T100.candidate_primes q hq, Decomp372c.bounds q hq⟩
  · exact offsets_certificate
      (fun d hd => le_trans (Decomp372c.offset_bounds d hd) (by norm_num)) Decomp372c.offset_cover


/-- P0037 page 211, the first interval family.
CONDITIONAL ON twelve new primary components and nine older prime batches.
The already proved rows 75, 80 and 85 are reused.
This is the exact Decomp121b.first_family_remaining statement. -/
theorem first_family_remaining :
    ∀ i : ℕ, 15 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8) := by
  intro i hlo hhi
  interval_cases i
  · obtain ⟨qs, _, hp, hc⟩ := certificate75
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := certificate80
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := certificate85
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := Decomp445d.certificate90
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := Decomp445d.certificate95
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := Decomp445d.certificate100
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc


/-- P0037 Theorem 2 page 206, both displayed interval families.
CONDITIONAL ON twelve new primary components, nine older prime batches
and eleven earlier Table 2 certificate leaves. The final assembly has
no sorry of its own and has the exact Decomp121b.theorem2 statement. -/
theorem theorem2 : FullTheorem2 :=
  Decomp121b.theorem2_of_remaining Decomp445d.first_family_remaining Decomp270c.second_family

#print axioms certificate90
#print axioms certificate95
#print axioms certificate100
#print axioms first_family_remaining
#print axioms theorem2

end LeanLab.DtRS1998.Decomp445d
