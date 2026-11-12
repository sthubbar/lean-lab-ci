/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part3

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window271000000 :
    ∀ j : ℕ, 271000000 ≤ j → j < 271560938 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 542000000) (x1 := 543121874) (lo := 542000069) (W := 1231515)
    (Ds := offsets.take 167) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window271000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window271560939 :
    ∀ j : ℕ, 271560939 ≤ j → j < 271861224 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543121878) (x1 := 543722446) (lo := 543121947) (W := 702049)
    (Ds := offsets.take 159) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window271560939

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window271861225 :
    ∀ j : ℕ, 271861225 ≤ j → j < 272000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 543722450) (x1 := 543999998) (lo := 543722519) (W := 391263)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window271861225

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window272000000 :
    ∀ j : ℕ, 272000000 ≤ j → j < 272175399 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544000000) (x1 := 544350796) (lo := 544000069) (W := 464511)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window272000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window272175400 :
    ∀ j : ℕ, 272175400 ≤ j → j < 272354738 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544350800) (x1 := 544709474) (lo := 544350869) (W := 447907)
    (Ds := offsets.take 137) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window272175400

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window272354739 :
    ∀ j : ℕ, 272354739 ≤ j → j < 273000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 544709478) (x1 := 545999998) (lo := 544709547) (W := 1407169)
    (Ds := offsets.take 178) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window272354739

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window273000000 :
    ∀ j : ℕ, 273000000 ≤ j → j < 274000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 546000000) (x1 := 547999998) (lo := 546000069) (W := 2116287)
    (Ds := offsets.take 177) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window273000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window274000000 :
    ∀ j : ℕ, 274000000 ≤ j → j < 275000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 548000000) (x1 := 549999998) (lo := 548000069) (W := 2118349)
    (Ds := offsets.take 182) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window274000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window275000000 :
    ∀ j : ℕ, 275000000 ≤ j → j < 276000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 550000000) (x1 := 551999998) (lo := 550000069) (W := 2123463)
    (Ds := offsets.take 185) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window275000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window276000000 :
    ∀ j : ℕ, 276000000 ≤ j → j < 277000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 552000000) (x1 := 553999998) (lo := 552000069) (W := 2132149)
    (Ds := offsets.take 197) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window276000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window277000000 :
    ∀ j : ℕ, 277000000 ≤ j → j < 278000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 554000000) (x1 := 555999998) (lo := 554000069) (W := 2125701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window277000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window278000000 :
    ∀ j : ℕ, 278000000 ≤ j → j < 279000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 556000000) (x1 := 557999998) (lo := 556000069) (W := 2131137)
    (Ds := offsets.take 194) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window278000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window279000000 :
    ∀ j : ℕ, 279000000 ≤ j → j < 280000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 558000000) (x1 := 559999998) (lo := 558000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window279000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window280000000 :
    ∀ j : ℕ, 280000000 ≤ j → j < 280647912 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 560000000) (x1 := 561295822) (lo := 560000069) (W := 1423055)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window280000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window280647913 :
    ∀ j : ℕ, 280647913 ≤ j → j < 281000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 561295826) (x1 := 561999998) (lo := 561295895) (W := 817887)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window280647913

end LeanLab.DtRS1998.CoverLower340Part3
