/-
AI wrote this Lean code for CODEX task303.
P0037 Section 4.1 pages 209 and 210. Strict first block subranges.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Task71Paper
import LeanLab.DtRS1998.Task303LowBlock
import LeanLab.DtRS1998.Task303Middle1Block
import LeanLab.DtRS1998.Task303Middle2Block
import LeanLab.DtRS1998.Task303HighBlock

namespace LeanLab.DtRS1998.Decomp270e

open LeanLab Task71.Paper

/-- The first closed subrange of width 10^8 in the first low block has a finite certificate.
P0037 Section 4.1 pages 209 and 210. This is a strict subrange of one block. -/
theorem cray_low_first_subrange :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 8) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 400000000000 + 2*j ∧ (400000000000 + 2*j - q).Prime))) = true := by
  exact Task303.Low.certificate

/-- Every even integer in this strict first block subrange is a prime sum.
P0037 Section 4.1 pages 209 and 210. -/
theorem cray_low_first_interval : IntervalSum 400000000000 (10 ^ 8) := by
  intro n hlo hhi he
  have hB : 2 ∣ 400000000000 := by decide
  have hx : 2 ∣ n - 400000000000 := Nat.dvd_sub (even_iff_two_dvd.mp he) hB
  obtain ⟨d, hd, hp⟩ := Task303.Low.all_offsets (n - 400000000000) (by omega) hx
  have hdB := Task303.Low.offset_bounds d hd
  have hm : 400000000000 - d ∈ Task303.Low.qs := by
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  exact ⟨400000000000 - d, n - 400000000000 + d, Task303.Low.all_primes _ hm, hp, by omega⟩

#print axioms cray_low_first_subrange
#print axioms cray_low_first_interval

/-- The first closed subrange of width 10^8 in the first middle1 block has a finite certificate.
P0037 Section 4.1 pages 209 and 210. This is a strict subrange of one block. -/
theorem cray_middle1_first_subrange :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 8) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 20000000000000 + 2*j ∧ (20000000000000 + 2*j - q).Prime))) = true := by
  exact Task303.Middle1.certificate

/-- Every even integer in this strict first block subrange is a prime sum.
P0037 Section 4.1 pages 209 and 210. -/
theorem cray_middle1_first_interval : IntervalSum 20000000000000 (10 ^ 8) := by
  intro n hlo hhi he
  have hB : 2 ∣ 20000000000000 := by decide
  have hx : 2 ∣ n - 20000000000000 := Nat.dvd_sub (even_iff_two_dvd.mp he) hB
  obtain ⟨d, hd, hp⟩ := Task303.Middle1.all_offsets (n - 20000000000000) (by omega) hx
  have hdB := Task303.Middle1.offset_bounds d hd
  have hm : 20000000000000 - d ∈ Task303.Middle1.qs := by
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  exact ⟨20000000000000 - d, n - 20000000000000 + d, Task303.Middle1.all_primes _ hm, hp, by omega⟩

#print axioms cray_middle1_first_subrange
#print axioms cray_middle1_first_interval

/-- The first closed subrange of width 10^8 in the first middle2 block has a finite certificate.
P0037 Section 4.1 pages 209 and 210. This is a strict subrange of one block. -/
theorem cray_middle2_first_subrange :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 8) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 60000000000000 + 2*j ∧ (60000000000000 + 2*j - q).Prime))) = true := by
  exact Task303.Middle2.certificate

/-- Every even integer in this strict first block subrange is a prime sum.
P0037 Section 4.1 pages 209 and 210. -/
theorem cray_middle2_first_interval : IntervalSum 60000000000000 (10 ^ 8) := by
  intro n hlo hhi he
  have hB : 2 ∣ 60000000000000 := by decide
  have hx : 2 ∣ n - 60000000000000 := Nat.dvd_sub (even_iff_two_dvd.mp he) hB
  obtain ⟨d, hd, hp⟩ := Task303.Middle2.all_offsets (n - 60000000000000) (by omega) hx
  have hdB := Task303.Middle2.offset_bounds d hd
  have hm : 60000000000000 - d ∈ Task303.Middle2.qs := by
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  exact ⟨60000000000000 - d, n - 60000000000000 + d, Task303.Middle2.all_primes _ hm, hp, by omega⟩

#print axioms cray_middle2_first_subrange
#print axioms cray_middle2_first_interval

/-- The first closed subrange of width 10^8 in the first high block has a finite certificate.
P0037 Section 4.1 pages 209 and 210. This is a strict subrange of one block. -/
theorem cray_high_first_subrange :
    ∃ qs : List ℕ, (∀ q ∈ qs, q.Prime) ∧
      (List.range ((10 ^ 8) / 2 + 1)).all (fun j =>
        qs.any (fun q => decide
          (q ≤ 90000000000000 + 2*j ∧ (90000000000000 + 2*j - q).Prime))) = true := by
  exact Task303.High.certificate

/-- Every even integer in this strict first block subrange is a prime sum.
P0037 Section 4.1 pages 209 and 210. -/
theorem cray_high_first_interval : IntervalSum 90000000000000 (10 ^ 8) := by
  intro n hlo hhi he
  have hB : 2 ∣ 90000000000000 := by decide
  have hx : 2 ∣ n - 90000000000000 := Nat.dvd_sub (even_iff_two_dvd.mp he) hB
  obtain ⟨d, hd, hp⟩ := Task303.High.all_offsets (n - 90000000000000) (by omega) hx
  have hdB := Task303.High.offset_bounds d hd
  have hm : 90000000000000 - d ∈ Task303.High.qs := by
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  exact ⟨90000000000000 - d, n - 90000000000000 + d, Task303.High.all_primes _ hm, hp, by omega⟩

#print axioms cray_high_first_subrange
#print axioms cray_high_first_interval

end LeanLab.DtRS1998.Decomp270e
