/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, bit array sieve paragraph.
Table 2 page 214 row 300. These are alternative certificate windows.
Every small prime is kernel checked. No large prime is asserted here.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455f

namespace LeanLab.DtRS1998.Decomp455h

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 131000000 through 131999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window131 : ∀ j : ℕ, 131000000 ≤ j → j < 132000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt131220198 : j < 131220198
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 262000000) (x1 := 262440394) (lo := 262000069) (W := 557043)
      (Ds := offsets.take 178) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq131220198 : j = 131220198
  · subst j
    refine ⟨3697757, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases hlt131250000 : j < 131250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 262440398) (x1 := 262499998) (lo := 262440467) (W := 176249)
      (Ds := offsets.take 178) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt131500000 : j < 131500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 262500000) (x1 := 262999998) (lo := 262500069) (W := 616647)
      (Ds := offsets.take 178) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt131750000 : j < 131750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 263000000) (x1 := 263499998) (lo := 263000069) (W := 616647)
      (Ds := offsets.take 178) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 263500000) (x1 := 263999998) (lo := 263500069) (W := 616647)
    (Ds := offsets.take 178) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 132000000 through 132999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window132 : ∀ j : ℕ, 132000000 ≤ j → j < 133000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt132250000 : j < 132250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 264000000) (x1 := 264499998) (lo := 264000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt132500000 : j < 132500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 264500000) (x1 := 264999998) (lo := 264500069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt132750000 : j < 132750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 265000000) (x1 := 265499998) (lo := 265000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 265500000) (x1 := 265999998) (lo := 265500069) (W := 623853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 133000000 through 133999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window133 : ∀ j : ℕ, 133000000 ≤ j → j < 134000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt133250000 : j < 133250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 266000000) (x1 := 266499998) (lo := 266000069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt133500000 : j < 133500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 266500000) (x1 := 266999998) (lo := 266500069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt133750000 : j < 133750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 267000000) (x1 := 267499998) (lo := 267000069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 267500000) (x1 := 267999998) (lo := 267500069) (W := 601479)
    (Ds := offsets.take 159) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 134000000 through 134999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window134 : ∀ j : ℕ, 134000000 ≤ j → j < 135000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt134250000 : j < 134250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 268000000) (x1 := 268499998) (lo := 268000069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt134500000 : j < 134500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 268500000) (x1 := 268999998) (lo := 268500069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt134750000 : j < 134750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 269000000) (x1 := 269499998) (lo := 269000069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 269500000) (x1 := 269999998) (lo := 269500069) (W := 631267)
    (Ds := offsets.take 195) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 135000000 through 135999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window135 : ∀ j : ℕ, 135000000 ≤ j → j < 136000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt135250000 : j < 135250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 270000000) (x1 := 270499998) (lo := 270000069) (W := 632149)
      (Ds := offsets.take 197) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt135500000 : j < 135500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 270500000) (x1 := 270999998) (lo := 270500069) (W := 632149)
      (Ds := offsets.take 197) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt135750000 : j < 135750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 271000000) (x1 := 271499998) (lo := 271000069) (W := 632149)
      (Ds := offsets.take 197) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 271500000) (x1 := 271999998) (lo := 271500069) (W := 632149)
    (Ds := offsets.take 197) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window131
#print axioms window132
#print axioms window133
#print axioms window134
#print axioms window135

end LeanLab.DtRS1998.Decomp455h
