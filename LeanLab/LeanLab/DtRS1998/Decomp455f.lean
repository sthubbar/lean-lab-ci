/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, bit array sieve paragraph.
These strict prefixes support the fixed certificate300 leaves.
They prove only small complement primality. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.Decomp455f

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The first million indices of coverage block 1 have listed prime complements.
This proves no primality assertion about 10 ^ 300 minus an offset. -/
theorem prefix1 : ∀ j : ℕ, 0 ≤ j → j < 1000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 0) (x1 := 1999998) (lo := 69) (W := 2073549)
    (Ds := offsets.take 112) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega)
    (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms prefix1

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The first million indices of coverage block 2 have listed prime complements.
This proves no primality assertion about 10 ^ 300 minus an offset. -/
theorem prefix2 : ∀ j : ℕ, 125000000 ≤ j → j < 126000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 250000000) (x1 := 251999998) (lo := 250000069) (W := 2113713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega)
    (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms prefix2

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The first million indices of coverage block 3 have listed prime complements.
This proves no primality assertion about 10 ^ 300 minus an offset. -/
theorem prefix3 : ∀ j : ℕ, 250000000 ≤ j → j < 251000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 500000000) (x1 := 501999998) (lo := 500000069) (W := 2127231)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega)
    (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms prefix3

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
The first million indices of coverage block 4 have listed prime complements.
This proves no primality assertion about 10 ^ 300 minus an offset. -/
theorem prefix4 : ∀ j : ℕ, 375000000 ≤ j → j < 376000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 750000000) (x1 := 751999998) (lo := 750000069) (W := 2504947)
    (Ds := offsets.take 205) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega)
    (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms prefix4

end LeanLab.DtRS1998.Decomp455f
