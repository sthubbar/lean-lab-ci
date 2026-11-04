/-
AI wrote this Lean code for CODEX task270.
P0037 Section 4.2 pages 210 and 211.
Each open leaf requests finite sieve certificates for one reported SGI range.
The arithmetic assembly is conditional on those certificates.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp270e

namespace LeanLab.DtRS1998.Decomp270f

open LeanLab Task71.Paper Decomp270a Decomp270e

/-- LEAF. P0037 Section 4.2 pages 210 and 211,
unnumbered range display and consecutive interval description.
Each of 78125 blocks of width 128 * 10 ^ 6 beginning at 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem sgi_low_blocks :
    ∀ k : ℕ, k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 4.2 pages 210 and 211,
unnumbered range display and consecutive interval description.
Each of 156250 blocks of width 128 * 10 ^ 6 beginning at 4 * 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem sgi_middle_blocks :
    ∀ k : ℕ, k < 156250 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (4 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- LEAF. P0037 Section 4.2 pages 210 and 211,
unnumbered range display and consecutive interval description.
Each of 78125 blocks of width 128 * 10 ^ 6 beginning at 8 * 10 ^ 13
has a certified prime list and a successful finite offset check.
These computation certificates are OPEN. -/
theorem sgi_high_blocks :
    ∀ k : ℕ, k < 78125 → ∃ qs : List ℕ,
      (∀ q ∈ qs, q.Prime) ∧
      (List.range ((128 * 10 ^ 6) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j ∧
            (8 * 10 ^ 13 + (128 * 10 ^ 6) * k + 2 * j - q).Prime))) = true := by
  sorry

/-- CONDITIONAL ON the 3 open SGI block certificate families.
P0037 Section 4.2 pages 210 and 211.
This is the exact statement of Decomp121.sgi_ranges. -/
theorem sgi_ranges :
    ∀ n : ℕ, Even n →
      ((10 ^ 13 ≤ n ∧ n ≤ 2 * 10 ^ 13) ∨
       (4 * 10 ^ 13 ≤ n ∧ n ≤ 6 * 10 ^ 13) ∨
       (8 * 10 ^ 13 ≤ n ∧ n ≤ 9 * 10 ^ 13)) → IsGoldbachSum n := by
  have h_low : IntervalSum (10 ^ 13) ((128 * 10 ^ 6) * 78125) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := sgi_low_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  have h_middle : IntervalSum (4 * 10 ^ 13) ((128 * 10 ^ 6) * 156250) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := sgi_middle_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  have h_high : IntervalSum (8 * 10 ^ 13) ((128 * 10 ^ 6) * 78125) := by
    apply interval_of_blocks (by decide)
    intro k hk
    obtain ⟨qs, hq, hc⟩ := sgi_high_blocks k hk
    exact interval_of_certificate
      (even_iff_two_dvd.mpr
        (dvd_add (by norm_num) (dvd_mul_of_dvd_left (by norm_num) k))) hq hc
  intro n he hr
  rcases hr with h0 | h1 | h2
  · apply h_low n h0.1 ?_ he
    norm_num at h0 ⊢
    omega
  · apply h_middle n h1.1 ?_ he
    norm_num at h1 ⊢
    omega
  · apply h_high n h2.1 ?_ he
    norm_num at h2 ⊢
    omega

#print axioms sgi_low_blocks

#print axioms sgi_middle_blocks

#print axioms sgi_high_blocks

#print axioms sgi_ranges

end LeanLab.DtRS1998.Decomp270f
