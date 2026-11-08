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
Every j from 246000000 through 246999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window246 : ∀ j : ℕ, 246000000 ≤ j → j < 247000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt246250000 : j < 246250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 492000000) (x1 := 492499998) (lo := 492000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt246500000 : j < 246500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 492500000) (x1 := 492999998) (lo := 492500069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt246750000 : j < 246750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 493000000) (x1 := 493499998) (lo := 493000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 493500000) (x1 := 493999998) (lo := 493500069) (W := 613713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 247000000 through 247999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window247 : ∀ j : ℕ, 247000000 ≤ j → j < 248000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt247250000 : j < 247250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 494000000) (x1 := 494499998) (lo := 494000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt247500000 : j < 247500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 494500000) (x1 := 494999998) (lo := 494500069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt247750000 : j < 247750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 495000000) (x1 := 495499998) (lo := 495000069) (W := 623853)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt247809714 : j < 247809714
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 495500000) (x1 := 495619426) (lo := 495500069) (W := 243281)
      (Ds := offsets.take 186) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq247809714 : j = 247809714
  · subst j
    refine ⟨969173, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 495619430) (x1 := 495999998) (lo := 495619499) (W := 504423)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 248000000 through 248999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window248 : ∀ j : ℕ, 248000000 ≤ j → j < 249000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt248250000 : j < 248250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 496000000) (x1 := 496499998) (lo := 496000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt248500000 : j < 248500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 496500000) (x1 := 496999998) (lo := 496500069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt248750000 : j < 248750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 497000000) (x1 := 497499998) (lo := 497000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 497500000) (x1 := 497999998) (lo := 497500069) (W := 613713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 249000000 through 249999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window249 : ∀ j : ℕ, 249000000 ≤ j → j < 250000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt249250000 : j < 249250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 498000000) (x1 := 498499998) (lo := 498000069) (W := 609639)
      (Ds := offsets.take 167) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt249500000 : j < 249500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 498500000) (x1 := 498999998) (lo := 498500069) (W := 609639)
      (Ds := offsets.take 167) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt249750000 : j < 249750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 499000000) (x1 := 499499998) (lo := 499000069) (W := 609639)
      (Ds := offsets.take 167) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 499500000) (x1 := 499999998) (lo := 499500069) (W := 609639)
    (Ds := offsets.take 167) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window246
#print axioms window247
#print axioms window248
#print axioms window249

end LeanLab.DtRS1998.Decomp455h
