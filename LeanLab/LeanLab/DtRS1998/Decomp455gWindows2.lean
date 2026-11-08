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
Every j from 11000000 through 11999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window11 : ∀ j : ℕ, 11000000 ≤ j → j < 12000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 22000000) (x1 := 23999998) (lo := 22000069) (W := 2090053)
    (Ds := offsets.take 138) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window11

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 12000000 through 12999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window12 : ∀ j : ℕ, 12000000 ≤ j → j < 13000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 24000000) (x1 := 25999998) (lo := 24000069) (W := 2098591)
    (Ds := offsets.take 152) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window12

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 13000000 through 13999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window13 : ∀ j : ℕ, 13000000 ≤ j → j < 14000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 26000000) (x1 := 27999998) (lo := 26000069) (W := 2109699)
    (Ds := offsets.take 168) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window13

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 14000000 through 14999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window14 : ∀ j : ℕ, 14000000 ≤ j → j < 15000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 28000000) (x1 := 29999998) (lo := 28000069) (W := 2100043)
    (Ds := offsets.take 155) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window14

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 15000000 through 15999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window15 : ∀ j : ℕ, 15000000 ≤ j → j < 16000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 30000000) (x1 := 31999998) (lo := 30000069) (W := 2112909)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window15

end LeanLab.DtRS1998.Decomp455g
