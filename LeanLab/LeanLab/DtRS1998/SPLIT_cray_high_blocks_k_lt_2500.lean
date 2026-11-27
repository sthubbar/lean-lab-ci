/-
Split of the sealed window statement cray_high_blocks_k_lt_2500 of
LeanLab.DtRS1998.SPLIT_cray_high_blocks.
The window of 2500 blocks is cut into five consecutive windows of 500 blocks each.
Each window is a finite certificate request on its own: a prime list and a Boolean
offset check on every even offset inside every block of that window.
The assembly is a case split on the window holding k; it adds no input.
-/

import LeanLab.DtRS1998.SPLIT_cray_high_blocks
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a
open LeanLab.DtRS1998.Certificate294

/-- LEAF. First sub-window of the 0..2499 block family: every block with k < 500
carries a finite prime list qs and a successful Boolean offset check, i.e. for each
j < (10 ^ 9) / 2 + 1 some q in qs satisfies
q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j and the difference is prime.
The prime list and the check are open. -/
theorem cray_high_blocks_k_lt_500 :
    ∀ k : ℕ, k < 500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  let B : ℕ := 9 * 10 ^ 13 + (10 ^ 9) * k
  obtain ⟨Ds, hD, hcover⟩ :
      ∃ Ds : List ℕ,
        (∀ d ∈ Ds, d ≤ B) ∧
        (∀ x, x ≤ 10 ^ 9 → 2 ∣ x → ∃ d ∈ Ds, (x + d).Prime) := by
    sorry
  have hcheck := offsets_certificate (B := B) (L := 10 ^ 9) hD hcover
  refine ⟨Ds.map (fun d => B - d), ?_, ?_⟩
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨d, hd, rfl⟩ := hq
    sorry
  · simpa [B] using hcheck

/-- LEAF. Second sub-window: every block with 500 ≤ k < 1000 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_500_1000 :
    ∀ k : ℕ, 500 ≤ k → k < 1000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Third sub-window: every block with 1000 ≤ k < 1500 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_1000_1500 :
    ∀ k : ℕ, 1000 ≤ k → k < 1500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fourth sub-window: every block with 1500 ≤ k < 2000 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_1500_2000 :
    ∀ k : ℕ, 1500 ≤ k → k < 2000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Fifth sub-window: every block with 2000 ≤ k < 2500 carries a finite
prime list qs and a successful Boolean offset check on every j < (10 ^ 9) / 2 + 1.
The prime list and the check are open. -/
theorem cray_high_blocks_k_2000_2500 :
    ∀ k : ℕ, 2000 ≤ k → k < 2500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- The sealed statement of cray_high_blocks_k_lt_2500, assembled from the five
sub-window leaves by a case split on the window that holds k. -/
theorem cray_high_blocks_k_lt_2500_split :
    ∀ k : ℕ, k < 2500 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k h2500
  by_cases h500 : k < 500
  · exact cray_high_blocks_k_lt_500 k h500
  · have h500' : 500 ≤ k := by omega
    by_cases h1000 : k < 1000
    · exact cray_high_blocks_k_500_1000 k h500' h1000
    · have h1000' : 1000 ≤ k := by omega
      by_cases h1500 : k < 1500
      · exact cray_high_blocks_k_1000_1500 k h1000' h1500
      · have h1500' : 1500 ≤ k := by omega
        by_cases h2000 : k < 2000
        · exact cray_high_blocks_k_1500_2000 k h1500' h2000
        · have h2000' : 2000 ≤ k := by omega
          exact cray_high_blocks_k_2000_2500 k h2000' h2500

end LeanLab.DtRS1998.Decomp270e
