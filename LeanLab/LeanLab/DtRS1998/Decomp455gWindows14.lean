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
set_option Elab.async true

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 71000000 through 71999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window71 : ∀ j : ℕ, 71000000 ≤ j → j < 72000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt71250000 : j < 71250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 142000000) (x1 := 142499998) (lo := 142000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt71500000 : j < 71500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 142500000) (x1 := 142999998) (lo := 142500069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt71750000 : j < 71750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 143000000) (x1 := 143499998) (lo := 143000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 143500000) (x1 := 143999998) (lo := 143500069) (W := 623853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window71

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 72000000 through 72999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window72 : ∀ j : ℕ, 72000000 ≤ j → j < 73000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt72250000 : j < 72250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 144000000) (x1 := 144499998) (lo := 144000069) (W := 609163)
      (Ds := offsets.take 164) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt72500000 : j < 72500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 144500000) (x1 := 144999998) (lo := 144500069) (W := 609163)
      (Ds := offsets.take 164) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt72750000 : j < 72750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 145000000) (x1 := 145499998) (lo := 145000069) (W := 609163)
      (Ds := offsets.take 164) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 145500000) (x1 := 145999998) (lo := 145500069) (W := 609163)
    (Ds := offsets.take 164) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window72

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 73000000 through 73999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window73 : ∀ j : ℕ, 73000000 ≤ j → j < 74000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt73250000 : j < 73250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 146000000) (x1 := 146499998) (lo := 146000069) (W := 600043)
      (Ds := offsets.take 155) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt73500000 : j < 73500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 146500000) (x1 := 146999998) (lo := 146500069) (W := 600043)
      (Ds := offsets.take 155) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt73750000 : j < 73750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 147000000) (x1 := 147499998) (lo := 147000069) (W := 600043)
      (Ds := offsets.take 155) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 147500000) (x1 := 147999998) (lo := 147500069) (W := 600043)
    (Ds := offsets.take 155) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window73

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 74000000 through 74999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window74 : ∀ j : ℕ, 74000000 ≤ j → j < 75000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt74250000 : j < 74250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 148000000) (x1 := 148499998) (lo := 148000069) (W := 612909)
      (Ds := offsets.take 172) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt74500000 : j < 74500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 148500000) (x1 := 148999998) (lo := 148500069) (W := 612909)
      (Ds := offsets.take 172) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt74750000 : j < 74750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 149000000) (x1 := 149499998) (lo := 149000069) (W := 612909)
      (Ds := offsets.take 172) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 149500000) (x1 := 149999998) (lo := 149500069) (W := 612909)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window74

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 75000000 through 75999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window75 : ∀ j : ℕ, 75000000 ≤ j → j < 76000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt75250000 : j < 75250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 150000000) (x1 := 150499998) (lo := 150000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt75500000 : j < 75500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 150500000) (x1 := 150999998) (lo := 150500069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt75750000 : j < 75750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 151000000) (x1 := 151499998) (lo := 151000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 151500000) (x1 := 151999998) (lo := 151500069) (W := 623853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window75

end LeanLab.DtRS1998.Decomp455g
