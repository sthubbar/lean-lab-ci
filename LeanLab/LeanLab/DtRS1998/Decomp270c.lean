/-
AI wrote this Lean code for CODEX task270.
P0037 Section 5.2 page 212 and Table 2 page 214.
The open leaves request prime lists and finite offset coverage checks.
Primality requires certificates, not Miller Rabin tests alone.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270b

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^260. At most 226 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate260 :
    ∃ qs : List ℕ, qs.length ≤ 226 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 260 + 2 * j ∧ (10 ^ 260 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^270. At most 223 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate270 :
    ∃ qs : List ℕ, qs.length ≤ 223 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^280. At most 225 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate280 :
    ∃ qs : List ℕ, qs.length ≤ 225 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 280 + 2 * j ∧ (10 ^ 280 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^290. At most 226 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate290 :
    ∃ qs : List ℕ, qs.length ≤ 226 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 290 + 2 * j ∧ (10 ^ 290 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^300. At most 227 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate300 :
    ∃ qs : List ℕ, qs.length ≤ 227 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 300 + 2 * j ∧ (10 ^ 300 + 2 * j - q).Prime))) = true := by
  sorry

/-- CONDITIONAL ON the eleven open Table 2 certificates.
P0037 Section 5.2 page 212 and Table 2 page 214.
This is the exact statement of Decomp121b.second_family. -/
theorem second_family :
    ∀ i : ℕ, 20 ≤ i → i ≤ 30 → IntervalSum (10 ^ (10 * i)) (10 ^ 9) := by
  intro i hlo hhi
  by_cases hlower : i ≤ 25
  · exact Decomp270b.second_family_lower i hlo hlower
  have hi : 26 ≤ i := by omega
  interval_cases i
  · obtain ⟨qs, _, hq, hc⟩ := certificate260
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate270
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate280
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate290
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate300
    exact interval_of_certificate (by decide) hq hc

#print axioms certificate260

#print axioms certificate270

#print axioms certificate280

#print axioms certificate290

#print axioms certificate300

#print axioms second_family

end LeanLab.DtRS1998.Decomp270c
