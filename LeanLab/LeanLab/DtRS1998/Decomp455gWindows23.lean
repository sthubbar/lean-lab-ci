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
Every j from 116000000 through 116999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window116 : ∀ j : ℕ, 116000000 ≤ j → j < 117000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt116250000 : j < 116250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 232000000) (x1 := 232499998) (lo := 232000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt116500000 : j < 116500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 232500000) (x1 := 232999998) (lo := 232500069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt116750000 : j < 116750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 233000000) (x1 := 233499998) (lo := 233000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 233500000) (x1 := 233999998) (lo := 233500069) (W := 623853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window116

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 117000000 through 117999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window117 : ∀ j : ℕ, 117000000 ≤ j → j < 118000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt117250000 : j < 117250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 234000000) (x1 := 234499998) (lo := 234000069) (W := 609699)
      (Ds := offsets.take 168) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt117500000 : j < 117500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 234500000) (x1 := 234999998) (lo := 234500069) (W := 609699)
      (Ds := offsets.take 168) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt117750000 : j < 117750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 235000000) (x1 := 235499998) (lo := 235000069) (W := 609699)
      (Ds := offsets.take 168) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 235500000) (x1 := 235999998) (lo := 235500069) (W := 609699)
    (Ds := offsets.take 168) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window117

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 118000000 through 118999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window118 : ∀ j : ℕ, 118000000 ≤ j → j < 119000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt118250000 : j < 118250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 236000000) (x1 := 236499998) (lo := 236000069) (W := 627231)
      (Ds := offsets.take 192) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt118260342 : j < 118260342
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 236500000) (x1 := 236520682) (lo := 236500069) (W := 147915)
      (Ds := offsets.take 192) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq118260342 : j = 118260342
  · subst j
    refine ⟨699059, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases hlt118500000 : j < 118500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 236520686) (x1 := 236999998) (lo := 236520755) (W := 606545)
      (Ds := offsets.take 192) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt118532013 : j < 118532013
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 237000000) (x1 := 237064024) (lo := 237000069) (W := 191257)
      (Ds := offsets.take 192) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq118532013 : j = 118532013
  · subst j
    refine ⟨3166973, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases hlt118750000 : j < 118750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 237064028) (x1 := 237499998) (lo := 237064097) (W := 563203)
      (Ds := offsets.take 192) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 237500000) (x1 := 237999998) (lo := 237500069) (W := 627231)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window118

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 119000000 through 119999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window119 : ∀ j : ℕ, 119000000 ≤ j → j < 120000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt119250000 : j < 119250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 238000000) (x1 := 238499998) (lo := 238000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt119500000 : j < 119500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 238500000) (x1 := 238999998) (lo := 238500069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt119750000 : j < 119750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 239000000) (x1 := 239499998) (lo := 239000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 239500000) (x1 := 239999998) (lo := 239500069) (W := 613713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window119

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 120000000 through 120999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block1 is checked. -/
theorem window120 : ∀ j : ℕ, 120000000 ≤ j → j < 121000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt120250000 : j < 120250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 240000000) (x1 := 240499998) (lo := 240000069) (W := 598401)
      (Ds := offsets.take 150) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt120500000 : j < 120500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 240500000) (x1 := 240999998) (lo := 240500069) (W := 598401)
      (Ds := offsets.take 150) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt120750000 : j < 120750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 241000000) (x1 := 241499998) (lo := 241000069) (W := 598401)
      (Ds := offsets.take 150) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 241500000) (x1 := 241999998) (lo := 241500069) (W := 598401)
    (Ds := offsets.take 150) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window120

end LeanLab.DtRS1998.Decomp455g
