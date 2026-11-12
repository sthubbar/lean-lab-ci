/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part1

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window251000000 :
    ∀ j : ℕ, 251000000 ≤ j → j < 252000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 502000000) (x1 := 503999998) (lo := 502000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window251000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window252000000 :
    ∀ j : ℕ, 252000000 ≤ j → j < 253000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 504000000) (x1 := 505999998) (lo := 504000069) (W := 2112909)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window252000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window253000000 :
    ∀ j : ℕ, 253000000 ≤ j → j < 254000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 506000000) (x1 := 507999998) (lo := 506000069) (W := 2127231)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window253000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window254000000 :
    ∀ j : ℕ, 254000000 ≤ j → j < 255000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 508000000) (x1 := 509999998) (lo := 508000069) (W := 2115247)
    (Ds := offsets.take 175) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window254000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window255000000 :
    ∀ j : ℕ, 255000000 ≤ j → j < 256000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 510000000) (x1 := 511999998) (lo := 510000069) (W := 2113713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window255000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window256000000 :
    ∀ j : ℕ, 256000000 ≤ j → j < 256264271 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512000000) (x1 := 512528540) (lo := 512000069) (W := 641451)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window256000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window256264272 :
    ∀ j : ℕ, 256264272 ≤ j → j < 257000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 512528544) (x1 := 513999998) (lo := 512528613) (W := 1597815)
    (Ds := offsets.take 191) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window256264272

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window257000000 :
    ∀ j : ℕ, 257000000 ≤ j → j < 258000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 514000000) (x1 := 515999998) (lo := 514000069) (W := 2127231)
    (Ds := offsets.take 192) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window257000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window258000000 :
    ∀ j : ℕ, 258000000 ≤ j → j < 259000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 516000000) (x1 := 517999998) (lo := 516000069) (W := 2116287)
    (Ds := offsets.take 177) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window258000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window259000000 :
    ∀ j : ℕ, 259000000 ≤ j → j < 260000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 518000000) (x1 := 519999998) (lo := 518000069) (W := 2116953)
    (Ds := offsets.take 179) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window259000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window260000000 :
    ∀ j : ℕ, 260000000 ≤ j → j < 261000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 520000000) (x1 := 521999998) (lo := 520000069) (W := 2122341)
    (Ds := offsets.take 183) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window260000000

end LeanLab.DtRS1998.CoverLower340Part1
