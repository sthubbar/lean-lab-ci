/-
F769: First window of the Cray low blocks (k < 2400).
P0037 Section 4.1 pages 209 and 210.

Target: for every k < 2400, there exists a finite prime list qs such that
for every even offset j < (10^9)/2 + 1, some q in qs satisfies
q ≤ B + 2*j and B + 2*j - q is prime, where B = 4*10^11 + 10^9*k.

This file splits the 2400 blocks into 24 groups of 100 consecutive blocks.
Each group has its own certificate (OPEN, a published computation).
The assembly combines them.
-/
import LeanLab.DtRS1998.Decomp270a

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-! ### Partition lemma -/

private theorem k_partition (k : ℕ) (hk : k < 2400) :
    k < 100 ∨ (100 ≤ k ∧ k < 200) ∨ (200 ≤ k ∧ k < 300) ∨ (300 ≤ k ∧ k < 400) ∨
      (400 ≤ k ∧ k < 500) ∨ (500 ≤ k ∧ k < 600) ∨ (600 ≤ k ∧ k < 700) ∨
      (700 ≤ k ∧ k < 800) ∨ (800 ≤ k ∧ k < 900) ∨ (900 ≤ k ∧ k < 1000) ∨
      (1000 ≤ k ∧ k < 1100) ∨ (1100 ≤ k ∧ k < 1200) ∨ (1200 ≤ k ∧ k < 1300) ∨
      (1300 ≤ k ∧ k < 1400) ∨ (1400 ≤ k ∧ k < 1500) ∨ (1500 ≤ k ∧ k < 1600) ∨
      (1600 ≤ k ∧ k < 1700) ∨ (1700 ≤ k ∧ k < 1800) ∨ (1800 ≤ k ∧ k < 1900) ∨
      (1900 ≤ k ∧ k < 2000) ∨ (2000 ≤ k ∧ k < 2100) ∨ (2100 ≤ k ∧ k < 2200) ∨
      (2200 ≤ k ∧ k < 2300) ∨ (2300 ≤ k ∧ k < 2400) := by
  omega

/-! ### LEAF 1: Structural reduction -/

/-- LEAF. Reduce offset covering to cray_low_blocks prime-list format.
Given offsets Ds covering all even x ≤ L with prime x + d,
construct qs = [B - d | d ∈ Ds] and verify the Boolean check.
-/
theorem leaf_offset_to_prime_list {B L : ℕ} {Ds : List ℕ}
    (hD : ∀ d ∈ Ds, d ≤ B)
    (hcover : ∀ x : ℕ, x ≤ L → 2 ∣ x → ∃ d ∈ Ds, (x + d).Prime) :
    ∃ qs : List ℕ,
      (List.range (L / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ B + 2 * j ∧ (B + 2 * j - q).Prime))) = true := by
  sorry

/-! ### LEAF 2-24: Group certificates (OPEN, published computation) -/

/-- LEAF. Blocks k = 0 to 99. Certificate works for all k in this range. -/
theorem leaf_k_0_99 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, k < 100 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 100 to 199. Certificate works for all k in this range. -/
theorem leaf_k_100_199 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 100 ≤ k → k < 200 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 200 to 299. Certificate works for all k in this range. -/
theorem leaf_k_200_299 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 200 ≤ k → k < 300 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 300 to 399. Certificate works for all k in this range. -/
theorem leaf_k_300_399 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 300 ≤ k → k < 400 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 400 to 499. Certificate works for all k in this range. -/
theorem leaf_k_400_499 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 400 ≤ k → k < 500 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 500 to 599. Certificate works for all k in this range. -/
theorem leaf_k_500_599 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 500 ≤ k → k < 600 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 600 to 699. Certificate works for all k in this range. -/
theorem leaf_k_600_699 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 600 ≤ k → k < 700 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 700 to 799. Certificate works for all k in this range. -/
theorem leaf_k_700_799 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 700 ≤ k → k < 800 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 800 to 899. Certificate works for all k in this range. -/
theorem leaf_k_800_899 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 800 ≤ k → k < 900 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 900 to 999. Certificate works for all k in this range. -/
theorem leaf_k_900_999 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 900 ≤ k → k < 1000 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1000 to 1099. Certificate works for all k in this range. -/
theorem leaf_k_1000_1099 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1000 ≤ k → k < 1100 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1100 to 1199. Certificate works for all k in this range. -/
theorem leaf_k_1100_1199 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1100 ≤ k → k < 1200 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1200 to 1299. Certificate works for all k in this range. -/
theorem leaf_k_1200_1299 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1200 ≤ k → k < 1300 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1300 to 1399. Certificate works for all k in this range. -/
theorem leaf_k_1300_1399 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1300 ≤ k → k < 1400 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1400 to 1499. Certificate works for all k in this range. -/
theorem leaf_k_1400_1499 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1400 ≤ k → k < 1500 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1500 to 1599. Certificate works for all k in this range. -/
theorem leaf_k_1500_1599 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1500 ≤ k → k < 1600 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1600 to 1699. Certificate works for all k in this range. -/
theorem leaf_k_1600_1699 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1600 ≤ k → k < 1700 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1700 to 1799. Certificate works for all k in this range. -/
theorem leaf_k_1700_1799 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1700 ≤ k → k < 1800 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1800 to 1899. Certificate works for all k in this range. -/
theorem leaf_k_1800_1899 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1800 ≤ k → k < 1900 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 1900 to 1999. Certificate works for all k in this range. -/
theorem leaf_k_1900_1999 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 1900 ≤ k → k < 2000 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 2000 to 2099. Certificate works for all k in this range. -/
theorem leaf_k_2000_2099 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 2000 ≤ k → k < 2100 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 2100 to 2199. Certificate works for all k in this range. -/
theorem leaf_k_2100_2199 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 2100 ≤ k → k < 2200 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 2200 to 2299. Certificate works for all k in this range. -/
theorem leaf_k_2200_2299 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 2200 ≤ k → k < 2300 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. Blocks k = 2300 to 2399. Certificate works for all k in this range. -/
theorem leaf_k_2300_2399 : ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
    ∀ k : ℕ, 2300 ≤ k → k < 2400 →
    (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
      qs.any (fun q => decide (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
        (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-! ### Assembly -/

/-- Assembly of the first window (k < 2400) from 24 group certificates.
Case-split on k to find the right group, then apply the group certificate. -/
theorem cray_low_blocks_k_lt_2400 :
    ∀ k : ℕ, k < 2400 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  intro k hk
  rcases k_partition k hk with
    h0 | h100 | h200 | h300 | h400 | h500 | h600 | h700 | h800 | h900 |
    h1000 | h1100 | h1200 | h1300 | h1400 | h1500 | h1600 | h1700 | h1800 | h1900 |
    h2000 | h2100 | h2200 | h2300
  · -- k < 100
    obtain ⟨qs, hq, hc⟩ := leaf_k_0_99
    exact ⟨qs, hq, hc k (by omega)⟩
  · -- 100 ≤ k < 200
    obtain ⟨qs, hq, hc⟩ := leaf_k_100_199
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 200 ≤ k < 300
    obtain ⟨qs, hq, hc⟩ := leaf_k_200_299
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 300 ≤ k < 400
    obtain ⟨qs, hq, hc⟩ := leaf_k_300_399
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 400 ≤ k < 500
    obtain ⟨qs, hq, hc⟩ := leaf_k_400_499
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 500 ≤ k < 600
    obtain ⟨qs, hq, hc⟩ := leaf_k_500_599
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 600 ≤ k < 700
    obtain ⟨qs, hq, hc⟩ := leaf_k_600_699
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 700 ≤ k < 800
    obtain ⟨qs, hq, hc⟩ := leaf_k_700_799
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 800 ≤ k < 900
    obtain ⟨qs, hq, hc⟩ := leaf_k_800_899
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 900 ≤ k < 1000
    obtain ⟨qs, hq, hc⟩ := leaf_k_900_999
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1000 ≤ k < 1100
    obtain ⟨qs, hq, hc⟩ := leaf_k_1000_1099
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1100 ≤ k < 1200
    obtain ⟨qs, hq, hc⟩ := leaf_k_1100_1199
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1200 ≤ k < 1300
    obtain ⟨qs, hq, hc⟩ := leaf_k_1200_1299
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1300 ≤ k < 1400
    obtain ⟨qs, hq, hc⟩ := leaf_k_1300_1399
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1400 ≤ k < 1500
    obtain ⟨qs, hq, hc⟩ := leaf_k_1400_1499
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1500 ≤ k < 1600
    obtain ⟨qs, hq, hc⟩ := leaf_k_1500_1599
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1600 ≤ k < 1700
    obtain ⟨qs, hq, hc⟩ := leaf_k_1600_1699
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1700 ≤ k < 1800
    obtain ⟨qs, hq, hc⟩ := leaf_k_1700_1799
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1800 ≤ k < 1900
    obtain ⟨qs, hq, hc⟩ := leaf_k_1800_1899
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 1900 ≤ k < 2000
    obtain ⟨qs, hq, hc⟩ := leaf_k_1900_1999
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 2000 ≤ k < 2100
    obtain ⟨qs, hq, hc⟩ := leaf_k_2000_2099
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 2100 ≤ k < 2200
    obtain ⟨qs, hq, hc⟩ := leaf_k_2100_2199
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 2200 ≤ k < 2300
    obtain ⟨qs, hq, hc⟩ := leaf_k_2200_2299
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩
  · -- 2300 ≤ k < 2400
    obtain ⟨qs, hq, hc⟩ := leaf_k_2300_2399
    exact ⟨qs, hq, hc k (by omega) (by omega)⟩

#print axioms cray_low_blocks_k_lt_2400

end LeanLab.DtRS1998.Decomp270e
