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
Every j from 171000000 through 171999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window171 : ∀ j : ℕ, 171000000 ≤ j → j < 172000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt171250000 : j < 171250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 342000000) (x1 := 342499998) (lo := 342000069) (W := 622341)
      (Ds := offsets.take 183) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt171500000 : j < 171500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 342500000) (x1 := 342999998) (lo := 342500069) (W := 622341)
      (Ds := offsets.take 183) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt171750000 : j < 171750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 343000000) (x1 := 343499998) (lo := 343000069) (W := 622341)
      (Ds := offsets.take 183) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 343500000) (x1 := 343999998) (lo := 343500069) (W := 622341)
    (Ds := offsets.take 183) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 172000000 through 172999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window172 : ∀ j : ℕ, 172000000 ≤ j → j < 173000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt172250000 : j < 172250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 344000000) (x1 := 344499998) (lo := 344000069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt172500000 : j < 172500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 344500000) (x1 := 344999998) (lo := 344500069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt172750000 : j < 172750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 345000000) (x1 := 345499998) (lo := 345000069) (W := 631267)
      (Ds := offsets.take 195) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 345500000) (x1 := 345999998) (lo := 345500069) (W := 631267)
    (Ds := offsets.take 195) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 173000000 through 173999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window173 : ∀ j : ℕ, 173000000 ≤ j → j < 174000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt173250000 : j < 173250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 346000000) (x1 := 346499998) (lo := 346000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt173500000 : j < 173500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 346500000) (x1 := 346999998) (lo := 346500069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt173750000 : j < 173750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 347000000) (x1 := 347499998) (lo := 347000069) (W := 613713)
      (Ds := offsets.take 173) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 347500000) (x1 := 347999998) (lo := 347500069) (W := 613713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 174000000 through 174999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window174 : ∀ j : ℕ, 174000000 ≤ j → j < 175000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt174250000 : j < 174250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 348000000) (x1 := 348499998) (lo := 348000069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt174500000 : j < 174500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 348500000) (x1 := 348999998) (lo := 348500069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt174750000 : j < 174750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 349000000) (x1 := 349499998) (lo := 349000069) (W := 601479)
      (Ds := offsets.take 159) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 349500000) (x1 := 349999998) (lo := 349500069) (W := 601479)
    (Ds := offsets.take 159) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

/-- P0037 Section 5.2 page 212, bit array sieve paragraph.
Every j from 175000000 through 175999999 has a prime complement in the fixed list.
Only this strict subrange of sealed cover_block2 is checked. -/
theorem window175 : ∀ j : ℕ, 175000000 ≤ j → j < 176000000 →
    ∃ a ∈ offsets, a ≤ 10 ^ 300 ∧ (2 * j + a).Prime := by
  intro j hj0 hj1
  by_cases hlt175250000 : j < 175250000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 350000000) (x1 := 350499998) (lo := 350000069) (W := 625701)
      (Ds := offsets.take 189) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt175482414 : j < 175482414
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 350500000) (x1 := 350964826) (lo := 350500069) (W := 590529)
      (Ds := offsets.take 189) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq175482414 : j = 175482414
  · subst j
    refine ⟨336179, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases hlt175500000 : j < 175500000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 350964830) (x1 := 350999998) (lo := 350964899) (W := 160871)
      (Ds := offsets.take 189) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases hlt175649142 : j < 175649142
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 351000000) (x1 := 351298282) (lo := 351000069) (W := 423985)
      (Ds := offsets.take 189) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  by_cases heq175649142 : j = 175649142
  · subst j
    refine ⟨1334189, by decide +kernel, offsets_le _ (by decide +kernel), ?_⟩
    exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩
  by_cases hlt175750000 : j < 175750000
  ·
    obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
      (x0 := 351298286) (x1 := 351499998) (lo := 351298355) (W := 327415)
      (Ds := offsets.take 189) (by decide)
      (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
      (by decide +kernel) (by decide +kernel)
      (x := 2 * j) (by omega) (by omega) (by omega)
    have hamem : a ∈ offsets := List.mem_of_mem_take ha
    exact ⟨a, hamem, offsets_le a hamem, hp⟩
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 351500000) (x1 := 351999998) (lo := 351500069) (W := 625701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  have hamem : a ∈ offsets := List.mem_of_mem_take ha
  exact ⟨a, hamem, offsets_le a hamem, hp⟩

#print axioms window171
#print axioms window172
#print axioms window173
#print axioms window174
#print axioms window175

end LeanLab.DtRS1998.Decomp455h
