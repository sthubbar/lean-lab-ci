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
Every j from 26000000 through 26999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window26 : ∀ j : ℕ, 26000000 ≤ j → j < 27000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 52000000) (x1 := 53999998) (lo := 52000069) (W := 2110357)
    (Ds := offsets.take 169) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window26

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 27000000 through 27999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window27 : ∀ j : ℕ, 27000000 ≤ j → j < 28000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 54000000) (x1 := 55999998) (lo := 54000069) (W := 2099409)
    (Ds := offsets.take 154) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window27

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 28000000 through 28999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window28 : ∀ j : ℕ, 28000000 ≤ j → j < 29000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 56000000) (x1 := 57999998) (lo := 56000069) (W := 2098027)
    (Ds := offsets.take 149) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window28

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 29000000 through 29999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window29 : ∀ j : ℕ, 29000000 ≤ j → j < 30000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 58000000) (x1 := 59999998) (lo := 58000069) (W := 2115147)
    (Ds := offsets.take 174) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window29

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 30000000 through 30999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window30 : ∀ j : ℕ, 30000000 ≤ j → j < 31000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 60000000) (x1 := 61999998) (lo := 60000069) (W := 2101479)
    (Ds := offsets.take 159) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window30

end LeanLab.DtRS1998.Decomp455g
