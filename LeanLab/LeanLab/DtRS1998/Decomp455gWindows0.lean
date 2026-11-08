/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, bit array sieve paragraph.
Table 2 page 214 row 300. These are alternative certificate windows.
Every small prime is kernel checked. No large prime is asserted here.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455f

namespace LeanLab.DtRS1998.Decomp455g

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 1000000 through 1999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window1 : ∀ j : ℕ, 1000000 ≤ j → j < 2000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 2000000) (x1 := 3999998) (lo := 2000069) (W := 2093359)
    (Ds := offsets.take 142) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window1

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 2000000 through 2999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window2 : ∀ j : ℕ, 2000000 ≤ j → j < 3000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 4000000) (x1 := 5999998) (lo := 4000069) (W := 2089231)
    (Ds := offsets.take 137) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window2

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 3000000 through 3999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window3 : ∀ j : ℕ, 3000000 ≤ j → j < 4000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 6000000) (x1 := 7999998) (lo := 6000069) (W := 2090673)
    (Ds := offsets.take 139) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window3

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 4000000 through 4999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window4 : ∀ j : ℕ, 4000000 ≤ j → j < 5000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 8000000) (x1 := 9999998) (lo := 8000069) (W := 2098401)
    (Ds := offsets.take 150) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window4

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 5000000 through 5999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window5 : ∀ j : ℕ, 5000000 ≤ j → j < 6000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 10000000) (x1 := 11999998) (lo := 10000069) (W := 2101479)
    (Ds := offsets.take 159) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window5

end LeanLab.DtRS1998.Decomp455g
