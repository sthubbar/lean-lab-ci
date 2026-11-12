/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part6

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window301000000 :
    ∀ j : ℕ, 301000000 ≤ j → j < 302000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 602000000) (x1 := 603999998) (lo := 602000069) (W := 2131119)
    (Ds := offsets.take 193) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window301000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window302000000 :
    ∀ j : ℕ, 302000000 ≤ j → j < 303000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 604000000) (x1 := 605999998) (lo := 604000069) (W := 2126359)
    (Ds := offsets.take 191) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window302000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window303000000 :
    ∀ j : ℕ, 303000000 ≤ j → j < 304000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 606000000) (x1 := 607999998) (lo := 606000069) (W := 2113713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window303000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window304000000 :
    ∀ j : ℕ, 304000000 ≤ j → j < 305000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 608000000) (x1 := 609999998) (lo := 608000069) (W := 2115147)
    (Ds := offsets.take 174) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window304000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window305000000 :
    ∀ j : ℕ, 305000000 ≤ j → j < 306000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 610000000) (x1 := 611999998) (lo := 610000069) (W := 2113713)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window305000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window306000000 :
    ∀ j : ℕ, 306000000 ≤ j → j < 306886241 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 612000000) (x1 := 613772480) (lo := 612000069) (W := 1889451)
    (Ds := offsets.take 180) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window306000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window306886242 :
    ∀ j : ℕ, 306886242 ≤ j → j < 307000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 613772484) (x1 := 613999998) (lo := 613772553) (W := 323533)
    (Ds := offsets.take 145) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window306886242

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window307000000 :
    ∀ j : ℕ, 307000000 ≤ j → j < 308000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 614000000) (x1 := 615999998) (lo := 614000069) (W := 2131267)
    (Ds := offsets.take 195) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window307000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window308000000 :
    ∀ j : ℕ, 308000000 ≤ j → j < 308391528 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616000000) (x1 := 616783054) (lo := 616000069) (W := 883207)
    (Ds := offsets.take 156) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window308000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window308391529 :
    ∀ j : ℕ, 308391529 ≤ j → j < 309000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 616783058) (x1 := 617999998) (lo := 616783127) (W := 1342643)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window308391529

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window309000000 :
    ∀ j : ℕ, 309000000 ≤ j → j < 309928518 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 618000000) (x1 := 619857034) (lo := 618000069) (W := 1970749)
    (Ds := offsets.take 173) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window309000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window309928519 :
    ∀ j : ℕ, 309928519 ≤ j → j < 310000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 619857038) (x1 := 619999998) (lo := 619857107) (W := 227941)
    (Ds := offsets.take 132) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window309928519

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window310000000 :
    ∀ j : ℕ, 310000000 ≤ j → j < 310067844 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620000000) (x1 := 620135686) (lo := 620000069) (W := 235097)
    (Ds := offsets.take 154) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window310000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window310067845 :
    ∀ j : ℕ, 310067845 ≤ j → j < 310559547 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 620135690) (x1 := 621119092) (lo := 620135759) (W := 1088151)
    (Ds := offsets.take 161) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window310067845

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window310559548 :
    ∀ j : ℕ, 310559548 ≤ j → j < 311000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 621119096) (x1 := 621999998) (lo := 621119165) (W := 992047)
    (Ds := offsets.take 171) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window310559548

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window311000000 :
    ∀ j : ℕ, 311000000 ≤ j → j < 312000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 622000000) (x1 := 623999998) (lo := 622000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window311000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window312000000 :
    ∀ j : ℕ, 312000000 ≤ j → j < 312500000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 624000000) (x1 := 624999998) (lo := 624000069) (W := 1112909)
    (Ds := offsets.take 172) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window312000000

end LeanLab.DtRS1998.CoverLower340Part6
