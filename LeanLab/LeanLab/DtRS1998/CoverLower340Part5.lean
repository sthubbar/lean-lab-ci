/-
AI wrote this Lean code for FREE-gh-copilot task340.
P0037 Section 5.2 page 212, supporting fixed-list sieve certificates.
The offset list is alternative certificate data, not a list printed in the paper.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a
import LeanLab.DtRS1998.Certificate294

namespace LeanLab.DtRS1998.CoverLower340Part5

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window291000000 :
    ∀ j : ℕ, 291000000 ≤ j → j < 292000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 582000000) (x1 := 583999998) (lo := 582000069) (W := 2123463)
    (Ds := offsets.take 185) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window291000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window292000000 :
    ∀ j : ℕ, 292000000 ≤ j → j < 293000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 584000000) (x1 := 585999998) (lo := 584000069) (W := 2123853)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window292000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window293000000 :
    ∀ j : ℕ, 293000000 ≤ j → j < 293187012 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586000000) (x1 := 586374022) (lo := 586000069) (W := 483723)
    (Ds := offsets.take 168) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window293000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window293187013 :
    ∀ j : ℕ, 293187013 ≤ j → j < 293495298 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586374026) (x1 := 586990594) (lo := 586374095) (W := 726209)
    (Ds := offsets.take 167) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window293187013

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window293495299 :
    ∀ j : ℕ, 293495299 ≤ j → j < 293799606 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 586990598) (x1 := 587599210) (lo := 586990667) (W := 713385)
    (Ds := offsets.take 162) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window293495299

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window293799607 :
    ∀ j : ℕ, 293799607 ≤ j → j < 294000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 587599214) (x1 := 587999998) (lo := 587599283) (W := 508047)
    (Ds := offsets.take 163) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window293799607

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window294000000 :
    ∀ j : ℕ, 294000000 ≤ j → j < 295000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 588000000) (x1 := 589999998) (lo := 588000069) (W := 2132149)
    (Ds := offsets.take 197) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window294000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window295000000 :
    ∀ j : ℕ, 295000000 ≤ j → j < 296000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 590000000) (x1 := 591999998) (lo := 590000069) (W := 2124379)
    (Ds := offsets.take 187) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window295000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window296000000 :
    ∀ j : ℕ, 296000000 ≤ j → j < 297000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 592000000) (x1 := 593999998) (lo := 592000069) (W := 2125701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window296000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window297000000 :
    ∀ j : ℕ, 297000000 ≤ j → j < 297598662 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 594000000) (x1 := 595197322) (lo := 594000069) (W := 1321177)
    (Ds := offsets.take 186) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window297000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window297598663 :
    ∀ j : ℕ, 297598663 ≤ j → j < 298000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 595197326) (x1 := 595999998) (lo := 595197395) (W := 912313)
    (Ds := offsets.take 167) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window297598663

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window298000000 :
    ∀ j : ℕ, 298000000 ≤ j → j < 299000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 596000000) (x1 := 597999998) (lo := 596000069) (W := 2110357)
    (Ds := offsets.take 169) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window298000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window299000000 :
    ∀ j : ℕ, 299000000 ≤ j → j < 300000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 598000000) (x1 := 599999998) (lo := 598000069) (W := 2125701)
    (Ds := offsets.take 189) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window299000000

/-- P0037 page 212, a bounded window of small prime companions. -/
theorem window300000000 :
    ∀ j : ℕ, 300000000 ≤ j → j < 301000000 →
      ∃ a ∈ offsets, (2 * j + a).Prime := by
  intro j hlo hj
  obtain ⟨a, ha, hp⟩ := Certificate294.offset_window
    (x0 := 600000000) (x1 := 601999998) (lo := 600000069) (W := 2125149)
    (Ds := offsets.take 188) (by decide)
    (by norm_num [LeanLab.Verifications.Top50.Bits.B2])
    (by decide +kernel) (by decide +kernel)
    (x := 2 * j) (by omega) (by omega) (by omega)
  exact ⟨a, List.mem_of_mem_take ha, hp⟩

#print axioms window300000000

end LeanLab.DtRS1998.CoverLower340Part5
