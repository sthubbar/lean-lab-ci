/-
AI wrote this Lean code for CODEX task270.
P0037 Section 4.1 pages 209 and 210.
Each open leaf requests finite sieve certificates for one reported Cray range.
The arithmetic assembly is conditional on those certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270a

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper Decomp270a

/-- P0037 Section 4.1 page 209, the paragraph on consecutive intervals.
Certificates on K consecutive closed blocks cover their combined interval.
This is CONDITIONAL ON the supplied blocks. -/
theorem interval_of_blocks {B D K : ℕ} (hK : 0 < K)
    (hblocks : ∀ k : ℕ, k < K → IntervalSum (B + D * k) D) :
    IntervalSum B (D * K) := by
  revert hK hblocks
  induction K with
  | zero => intro hK; omega
  | succ K ih =>
    intro hK hblocks
    by_cases hz : K = 0
    · subst K
      simpa using hblocks 0 (by decide)
    have hpre := ih (by omega) (fun k hk => hblocks k (by omega))
    intro n hlo hhi he
    by_cases hn : n ≤ B + D * K
    · exact hpre n hlo hn he
    · apply hblocks K (by omega) n (by omega) ?_ he
      simpa [Nat.mul_succ, Nat.add_assoc] using hhi

/-- LEAF. P0037 Section 4.1 pages 209 and 210,
unnumbered range display and consecutive interval description.
Each of 9600 blocks of width 10 ^ 9 beginning at 4 * 10 ^ 11
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem cray_low_blocks :
    ∀ k : ℕ, k < 9600 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j ∧
            (4 * 10 ^ 11 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 4.1 pages 209 and 210,
unnumbered range display and consecutive interval description.
Each of 20000 blocks of width 10 ^ 9 beginning at 2 * 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem cray_middle1_blocks :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (2 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 4.1 pages 209 and 210,
unnumbered range display and consecutive interval description.
Each of 20000 blocks of width 10 ^ 9 beginning at 6 * 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem cray_middle2_blocks :
    ∀ k : ℕ, k < 20000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (6 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 4.1 pages 209 and 210,
unnumbered range display and consecutive interval description.
Each of 10000 blocks of width 10 ^ 9 beginning at 9 * 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem cray_high_blocks :
    ∀ k : ℕ, k < 10000 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 9) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j ∧
            (9 * 10 ^ 13 + (10 ^ 9) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- CONDITIONAL ON the 4 open CRAY block certificate families.
P0037 Section 4.1 pages 209 and 210.
This is the exact statement of Decomp121.cray_ranges. -/
theorem cray_ranges :
    ∀ n : ℕ, Even n →
      ((4 * 10 ^ 11 ≤ n ∧ n ≤ 10 ^ 13) ∨
       (2 * 10 ^ 13 ≤ n ∧ n ≤ 4 * 10 ^ 13) ∨
       (6 * 10 ^ 13 ≤ n ∧ n ≤ 8 * 10 ^ 13) ∨
       (9 * 10 ^ 13 ≤ n ∧ n ≤ 10 ^ 14)) → IsGoldbachSum n := by
  have h_low : IntervalSum (4 * 10 ^ 11) ((10 ^ 9) * 9600) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := cray_low_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  have h_middle1 : IntervalSum (2 * 10 ^ 13) ((10 ^ 9) * 20000) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := cray_middle1_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  have h_middle2 : IntervalSum (6 * 10 ^ 13) ((10 ^ 9) * 20000) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := cray_middle2_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  have h_high : IntervalSum (9 * 10 ^ 13) ((10 ^ 9) * 10000) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := cray_high_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  intro n he hr
  rcases hr with h0 | h1 | h2 | h3
  · apply h_low n h0.1 ?_ he
    norm_num at h0 ⊢
    omega
  · apply h_middle1 n h1.1 ?_ he
    norm_num at h1 ⊢
    omega
  · apply h_middle2 n h2.1 ?_ he
    norm_num at h2 ⊢
    omega
  · apply h_high n h3.1 ?_ he
    norm_num at h3 ⊢
    omega

#print axioms interval_of_blocks

#print axioms cray_low_blocks

#print axioms cray_middle1_blocks

#print axioms cray_middle2_blocks

#print axioms cray_high_blocks

#print axioms cray_ranges

end LeanLab.DtRS1998.Decomp270e
