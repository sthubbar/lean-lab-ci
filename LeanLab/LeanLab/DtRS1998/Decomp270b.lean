/-
AI wrote this Lean code for CODEX task270.
P0037 Section 5.2 page 212 and Table 2 page 214.
The open leaves request prime lists and finite offset coverage checks.
Primality requires certificates, not Miller Rabin tests alone.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270a

namespace LeanLab.DtRS1998.Decomp270b

open LeanLab Task71.Paper Decomp270a

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^200. At most 224 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate200 :
    ∃ qs : List ℕ, qs.length ≤ 224 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 200 + 2 * j ∧ (10 ^ 200 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^210. At most 222 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate210 :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 210 + 2 * j ∧ (10 ^ 210 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^220. At most 222 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate220 :
    ∃ qs : List ℕ, qs.length ≤ 222 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 220 + 2 * j ∧ (10 ^ 220 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^230. At most 228 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate230 :
    ∃ qs : List ℕ, qs.length ≤ 228 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 230 + 2 * j ∧ (10 ^ 230 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^240. At most 228 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate240 :
    ∃ qs : List ℕ, qs.length ≤ 228 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 240 + 2 * j ∧ (10 ^ 240 + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 5.2 page 212, unnumbered interval display,
Table 2 page 214, row 10^250. At most 231 certified primes
cover all even offsets through 10^9. No ordering of the list is assumed.
The ECPP prime certificates and finite coverage check are OPEN. -/
theorem certificate250 :
    ∃ qs : List ℕ, qs.length ≤ 231 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (List.range (10 ^ 9 / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 250 + 2 * j ∧ (10 ^ 250 + 2 * j - q).Prime))) = true := by
  sorry

/-- CONDITIONAL ON the six open certificates for exponents 200 through 250.
P0037 Section 5.2 page 212 and Table 2 page 214. -/
theorem second_family_lower :
    ∀ i : ℕ, 20 ≤ i → i ≤ 25 → IntervalSum (10 ^ (10 * i)) (10 ^ 9) := by
  intro i hlo hhi
  interval_cases i
  · obtain ⟨qs, _, hq, hc⟩ := certificate200
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate210
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate220
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate230
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate240
    exact interval_of_certificate (by decide) hq hc
  · obtain ⟨qs, _, hq, hc⟩ := certificate250
    exact interval_of_certificate (by decide) hq hc

#print axioms certificate200

#print axioms certificate210

#print axioms certificate220

#print axioms certificate230

#print axioms certificate240

#print axioms certificate250

#print axioms second_family_lower

end LeanLab.DtRS1998.Decomp270b
