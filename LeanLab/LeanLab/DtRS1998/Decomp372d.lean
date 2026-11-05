/-
AI wrote this Lean code for CODEX task372.
P0037 Theorem 2 page 206 and Sections 5.1 and 5.2 pages 211 to 214.
This assembly uses the three fixed-list decompositions and the earlier leaves.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372a
import LeanLab.DtRS1998.Decomp372b
import LeanLab.DtRS1998.Decomp372c
import LeanLab.DtRS1998.Decomp270d

namespace LeanLab.DtRS1998.Decomp372d

open Task71.Paper Decomp270a

/-- CONDITIONAL ON the three open candidate primality leaves in Decomp372a through Decomp372c.
P0037 Section 5.1 page 211 and Table 1 page 213.
This is the exact statement of Decomp121b.first_family_remaining. -/
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
  · obtain ⟨qs, _, hp, hc⟩ := Decomp372a.certificate90
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := Decomp372b.certificate95
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc
  · obtain ⟨qs, _, hp, hc⟩ := Decomp372c.certificate100
    exact interval_of_certificate (by decide) (fun q h => (hp q h).1) hc

/-- CONDITIONAL ON the three candidate primality leaves and eleven earlier Table 2 certificates.
P0037 Theorem 2 page 206, both interval displays.
This is the exact statement of Decomp121b.theorem2.
No old first_family_remaining or second_family sorry proof is used. -/
theorem theorem2 : FullTheorem2 :=
  Decomp121b.theorem2_of_remaining Decomp372d.first_family_remaining Decomp270c.second_family

#print axioms first_family_remaining
#print axioms theorem2

end LeanLab.DtRS1998.Decomp372d
