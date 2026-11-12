/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part2

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window261000000 :
    ∀ j : ℕ, 261000000 ≤ j → j < 262000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 522000000) (x1 := 523999998) (lo := 522000069) (W := 2127231)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window261000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window262000000 :
    ∀ j : ℕ, 262000000 ≤ j → j < 263000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 524000000) (x1 := 525999998) (lo := 524000069) (W := 2118037)
    (Ds := offsets.take 181) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window262000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window263000000 :
    ∀ j : ℕ, 263000000 ≤ j → j < 263513682 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 526000000) (x1 := 527027362) (lo := 526000069) (W := 1144317)
    (Ds := offsets.take 179) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window263000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window263513683 :
    ∀ j : ℕ, 263513683 ≤ j → j < 264000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 527027366) (x1 := 527999998) (lo := 527027435) (W := 1081797)
    (Ds := offsets.take 164) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window263513683

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window264000000 :
    ∀ j : ℕ, 264000000 ≤ j → j < 265000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 528000000) (x1 := 529999998) (lo := 528000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window264000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window265000000 :
    ∀ j : ℕ, 265000000 ≤ j → j < 265573404 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 530000000) (x1 := 531146806) (lo := 530000069) (W := 1249035)
    (Ds := offsets.take 160) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window265000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window265573405 :
    ∀ j : ℕ, 265573405 ≤ j → j < 266000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 531146810) (x1 := 531999998) (lo := 531146879) (W := 962401)
    (Ds := offsets.take 166) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window265573405

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window266000000 :
    ∀ j : ℕ, 266000000 ≤ j → j < 267000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 532000000) (x1 := 533999998) (lo := 532000069) (W := 2125701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window266000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window267000000 :
    ∀ j : ℕ, 267000000 ≤ j → j < 268000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 534000000) (x1 := 535999998) (lo := 534000069) (W := 2116287)
    (Ds := offsets.take 177) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window267000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window268000000 :
    ∀ j : ℕ, 268000000 ≤ j → j < 269000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 536000000) (x1 := 537999998) (lo := 536000069) (W := 2123853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window268000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window269000000 :
    ∀ j : ℕ, 269000000 ≤ j → j < 269338358 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538000000) (x1 := 538676714) (lo := 538000069) (W := 800569)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window269000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window269338359 :
    ∀ j : ℕ, 269338359 ≤ j → j < 270000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 538676718) (x1 := 539999998) (lo := 538676787) (W := 1432981)
    (Ds := offsets.take 168) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window269338359

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window270000000 :
    ∀ j : ℕ, 270000000 ≤ j → j < 271000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 540000000) (x1 := 541999998) (lo := 540000069) (W := 2125701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window270000000

end LeanLab.DtRS1998.CoverLower340Part2
