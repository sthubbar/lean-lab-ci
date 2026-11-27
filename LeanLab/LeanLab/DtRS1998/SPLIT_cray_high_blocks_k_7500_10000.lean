/-
Split of the leaf cray_high_blocks_k_7500_10000 of LeanLab.DtRS1998.SPLIT_cray_high_blocks.
The window of 2500 blocks is cut into five consecutive windows of 500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window that holds k; it adds no input.
AI wrote the Lean code. Binary Goldbach is open.
-/

import LeanLab.Common.Goldbach

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab

/-- P0037 Section 4.1 pages 209 and 210. With no bound on the prime list length,
the finite certificate is equivalent to prime pairs at every offset.
The proof converts the Booleans symbolically, without evaluating the range. -/
theorem finite_prime_certificate_iff_goldbach (B L : ℕ) :
    (∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range (L / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true) ↔
    ∀ j < L / 2 + 1, IsGoldbachSum (B + 2 * j) := by
  constructor
  · rintro ⟨qs, hprime, hcheck⟩ j hj
    obtain ⟨q, hmem, hgood⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hcheck j (List.mem_range.mpr hj))
    have hpair := of_decide_eq_true hgood
    exact ⟨q, B + 2 * j - q, hprime q hmem, hpair.2,
      Nat.add_sub_of_le hpair.1⟩
  · intro h
    refine ⟨(List.range (B + L + 1)).filter (fun q => decide q.Prime), ?_, ?_⟩
    · intro q hq
      exact of_decide_eq_true (List.mem_filter.mp hq).2
    · apply List.all_eq_true.mpr
      intro j hj
      have hjlt := List.mem_range.mp hj
      have hjL : 2 * j ≤ L := by omega
      obtain ⟨p, q, hp, hq, hpq⟩ := h j hjlt
      apply List.any_eq_true.mpr
      refine ⟨p, List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), decide_eq_true hp⟩, ?_⟩
      apply decide_eq_true
      refine ⟨by omega, ?_⟩
      convert hq using 1
      omega

example : ∀ j < 4 / 2 + 1, IsGoldbachSum (6 + 2 * j) :=
  (finite_prime_certificate_iff_goldbach 6 4).mp
    ⟨[3, 5], by decide, by decide⟩

/-- LEAF. First sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 7500 ≤ k < 8000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_7500_8000 :
    ∀ k : ℕ, 7500 ≤ k → k < 8000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k _ _
  apply (finite_prime_certificate_iff_goldbach
    (9 * 10 ^ 13 + (10 ^ 9) * k) (10 ^ 9)).mpr
  sorry

/-- LEAF. Second sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 8000 ≤ k < 8500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_8000_8500 :
    ∀ k : ℕ, 8000 ≤ k → k < 8500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k _ _
  apply (finite_prime_certificate_iff_goldbach
    (9 * 10 ^ 13 + (10 ^ 9) * k) (10 ^ 9)).mpr
  sorry

/-- LEAF. Third sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 8500 ≤ k < 9000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_8500_9000 :
    ∀ k : ℕ, 8500 ≤ k → k < 9000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k _ _
  apply (finite_prime_certificate_iff_goldbach
    (9 * 10 ^ 13 + (10 ^ 9) * k) (10 ^ 9)).mpr
  sorry

/-- LEAF. Fourth sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 9000 ≤ k < 9500. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_9000_9500 :
    ∀ k : ℕ, 9000 ≤ k → k < 9500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k _ _
  apply (finite_prime_certificate_iff_goldbach
    (9 * 10 ^ 13 + (10 ^ 9) * k) (10 ^ 9)).mpr
  sorry

/-- LEAF. Fifth sub-window of the fourth high band, the step that supplies the certificate
for the blocks k with 9500 ≤ k < 10000. Every such block carries a finite prime list qs and a
successful Boolean offset check: for each j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference
9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q is prime. The prime list and the check are open. -/
theorem cray_high_blocks_k_9500_10000 :
    ∀ k : ℕ, 9500 ≤ k → k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k _ _
  apply (finite_prime_certificate_iff_goldbach
    (9 * 10 ^ 13 + (10 ^ 9) * k) (10 ^ 9)).mpr
  sorry

/-- The statement of cray_high_blocks_k_7500_10000, assembled from the five sub-window
leaves by a case split on the sub-window that holds k. -/
theorem cray_high_blocks_k_7500_10000_split :
    ∀ k : ℕ, 7500 ≤ k → k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h0 hk
  by_cases h1 : k < 8000
  · exact cray_high_blocks_k_7500_8000 k h0 h1
  · have h1g : 8000 ≤ k := by omega
    by_cases h2 : k < 8500
    · exact cray_high_blocks_k_8000_8500 k h1g h2
    · have h2g : 8500 ≤ k := by omega
      by_cases h3 : k < 9000
      · exact cray_high_blocks_k_8500_9000 k h2g h3
      · have h3g : 9000 ≤ k := by omega
        by_cases h4 : k < 9500
        · exact cray_high_blocks_k_9000_9500 k h3g h4
        · have h4g : 9500 ≤ k := by omega
          by_cases h5 : k < 10000
          · exact cray_high_blocks_k_9500_10000 k h4g h5
          · exact absurd hk h5

#print axioms finite_prime_certificate_iff_goldbach

end LeanLab.DtRS1998.Decomp270e
