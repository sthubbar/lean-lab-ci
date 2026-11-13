/-
AI wrote this Lean code for FREE-nv-minimax task342.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.CoverUpper342Bitmap

namespace LeanLab.DtRS1998.CoverUpper342Part1

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window312500000 :
    ∀ j : ℕ, 312500000 ≤ j → j < 313500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 625000000) (x1 := 626999998) (lo := 625000069) (W := 2118037)
    (Ds := offsets.take 181) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window312500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window313500000 :
    ∀ j : ℕ, 313500000 ≤ j → j < 314500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 627000000) (x1 := 628999998) (lo := 627000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window313500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window314500000 :
    ∀ j : ℕ, 314500000 ≤ j → j < 315500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 629000000) (x1 := 630999998) (lo := 629000069) (W := 2131267)
    (Ds := offsets.take 195) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window314500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window315500000 :
    ∀ j : ℕ, 315500000 ≤ j → j < 316500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 631000000) (x1 := 632999998) (lo := 631000069) (W := 2133321)
    (Ds := offsets.take 200) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window315500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window316500000 :
    ∀ j : ℕ, 316500000 ≤ j → j < 317500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 633000000) (x1 := 634999998) (lo := 633000069) (W := 2126359)
    (Ds := offsets.take 191) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window316500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window317500000 :
    ∀ j : ℕ, 317500000 ≤ j → j < 318500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 635000000) (x1 := 636999998) (lo := 635000069) (W := 3668343)
    (Ds := offsets.take 209) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window317500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window318500000 :
    ∀ j : ℕ, 318500000 ≤ j → j < 319500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 637000000) (x1 := 638999998) (lo := 637000069) (W := 2116287)
    (Ds := offsets.take 177) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window318500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window319500000 :
    ∀ j : ℕ, 319500000 ≤ j → j < 320500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 639000000) (x1 := 640999998) (lo := 639000069) (W := 2116953)
    (Ds := offsets.take 179) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window319500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window320500000 :
    ∀ j : ℕ, 320500000 ≤ j → j < 321500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 641000000) (x1 := 642999998) (lo := 641000069) (W := 2131119)
    (Ds := offsets.take 193) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window320500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window321500000 :
    ∀ j : ℕ, 321500000 ≤ j → j < 322500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 643000000) (x1 := 644999998) (lo := 643000069) (W := 3334119)
    (Ds := offsets.take 208) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window321500000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window322500000 :
    ∀ j : ℕ, 322500000 ≤ j → j < 323500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := CoverUpper342Bitmap.offset_window
    (x0 := 645000000) (x1 := 646999998) (lo := 645000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window322500000

end LeanLab.DtRS1998.CoverUpper342Part1
