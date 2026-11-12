/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part4

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window281000000 :
    ∀ j : ℕ, 281000000 ≤ j → j < 281971479 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 562000000) (x1 := 563942956) (lo := 562000069) (W := 2070189)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window281000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window281971480 :
    ∀ j : ℕ, 281971480 ≤ j → j < 282000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 563942960) (x1 := 563999998) (lo := 563943029) (W := 133973)
    (Ds := offsets.take 117) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window281971480

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window282000000 :
    ∀ j : ℕ, 282000000 ≤ j → j < 283000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 564000000) (x1 := 565999998) (lo := 564000069) (W := 2133321)
    (Ds := offsets.take 200) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window282000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window283000000 :
    ∀ j : ℕ, 283000000 ≤ j → j < 284000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 566000000) (x1 := 567999998) (lo := 566000069) (W := 2116287)
    (Ds := offsets.take 177) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window283000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window284000000 :
    ∀ j : ℕ, 284000000 ≤ j → j < 284199837 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568000000) (x1 := 568399672) (lo := 568000069) (W := 512583)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window284000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window284199838 :
    ∀ j : ℕ, 284199838 ≤ j → j < 285000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 568399676) (x1 := 569999998) (lo := 568399745) (W := 1714037)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window284199838

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window285000000 :
    ∀ j : ℕ, 285000000 ≤ j → j < 286000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 570000000) (x1 := 571999998) (lo := 570000069) (W := 2113713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window285000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window286000000 :
    ∀ j : ℕ, 286000000 ≤ j → j < 287000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 572000000) (x1 := 573999998) (lo := 572000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window286000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window287000000 :
    ∀ j : ℕ, 287000000 ≤ j → j < 288000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 574000000) (x1 := 575999998) (lo := 574000069) (W := 2122341)
    (Ds := offsets.take 183) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window287000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window288000000 :
    ∀ j : ℕ, 288000000 ≤ j → j < 289000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 576000000) (x1 := 577999998) (lo := 576000069) (W := 2115147)
    (Ds := offsets.take 174) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window288000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window289000000 :
    ∀ j : ℕ, 289000000 ≤ j → j < 290000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 578000000) (x1 := 579999998) (lo := 578000069) (W := 2118037)
    (Ds := offsets.take 181) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window289000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window290000000 :
    ∀ j : ℕ, 290000000 ≤ j → j < 291000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 580000000) (x1 := 581999998) (lo := 580000069) (W := 2112909)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window290000000

end LeanLab.DtRS1998.CoverLower340Part4
