/-
U-1385, run PC 20261021T0803Z-19426. Assembly of the memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
The two headline theorems are restated with the original statements and proofs, from the
windows in Part1 to Part8; row 23 is chained from windows. AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.Tables
import LeanLab.Verifications.Top50.SmallGB
import LeanLab.OeSHP2014.OeSHP2014U1385Part1
import LeanLab.OeSHP2014.OeSHP2014U1385Part2
import LeanLab.OeSHP2014.OeSHP2014U1385Part3
import LeanLab.OeSHP2014.OeSHP2014U1385Part8

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Leastness: below each Table 4 row with n ≤ 10000000, every even m has a smaller p(m). -/
theorem table4_least : ∀ x ∈ table4, x.1 ≤ 10000000 → ∀ m, Even m → 4 ≤ m → m < x.1 →
    minGB m < x.2 := by
  intro x hx
  simp only [table4, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_0 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_1 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_2 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_3 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_4 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_5 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_6 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_7 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_8 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_9 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_10 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_11 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_12 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_13 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_14 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_15 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_16 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_17 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_18 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_19 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_20 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_21 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_22 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)
  · intro h; exact absurd h (by norm_num)

/-- Completeness: every even m with 6 ≤ m ≤ 10000000 is bounded by a Table 4 row at or below m. -/
theorem table4_complete : ∀ m, Even m → 6 ≤ m → m ≤ 10000000 →
    ∃ x ∈ table4, x.1 ≤ m ∧ minGB m ≤ x.2 := by
  intro m hm h6 hmN
  rcases Nat.lt_or_ge m 12 with h1 | h1
  · exact ⟨(6, 3), by simp [table4], by omega, minGB_le_of_small seg_1 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 30 with h2 | h2
  · exact ⟨(12, 5), by simp [table4], by omega, minGB_le_of_small seg_2 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 98 with h3 | h3
  · exact ⟨(30, 7), by simp [table4], by omega, minGB_le_of_small seg_3 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 220 with h4 | h4
  · exact ⟨(98, 19), by simp [table4], by omega, minGB_le_of_small seg_4 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 308 with h5 | h5
  · exact ⟨(220, 23), by simp [table4], by omega, minGB_le_of_small seg_5 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 556 with h6 | h6
  · exact ⟨(308, 31), by simp [table4], by omega, minGB_le_of_small seg_6 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 992 with h7 | h7
  · exact ⟨(556, 47), by simp [table4], by omega, minGB_le_of_small seg_7 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 2642 with h8 | h8
  · exact ⟨(992, 73), by simp [table4], by omega, minGB_le_of_small seg_8 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 5372 with h9 | h9
  · exact ⟨(2642, 103), by simp [table4], by omega, minGB_le_of_small seg_9 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 7426 with h10 | h10
  · exact ⟨(5372, 139), by simp [table4], by omega, minGB_le_of_small seg_10 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 43532 with h11 | h11
  · exact ⟨(7426, 173), by simp [table4], by omega, minGB_le_of_small seg_11 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 54244 with h12 | h12
  · exact ⟨(43532, 211), by simp [table4], by omega, minGB_le_of_small seg_12 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 63274 with h13 | h13
  · exact ⟨(54244, 233), by simp [table4], by omega, minGB_le_of_small seg_13 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 113672 with h14 | h14
  · exact ⟨(63274, 293), by simp [table4], by omega, minGB_le_of_small seg_14 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 128168 with h15 | h15
  · exact ⟨(113672, 313), by simp [table4], by omega, minGB_le_of_small seg_15 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 194428 with h16 | h16
  · exact ⟨(128168, 331), by simp [table4], by omega, minGB_le_of_small seg_16 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 194470 with h17 | h17
  · exact ⟨(194428, 359), by simp [table4], by omega, minGB_le_of_small seg_17 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 413572 with h18 | h18
  · exact ⟨(194470, 383), by simp [table4], by omega, minGB_le_of_small seg_18 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 503222 with h19 | h19
  · exact ⟨(413572, 389), by simp [table4], by omega, minGB_le_of_small seg_19 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 1077422 with h20 | h20
  · exact ⟨(503222, 523), by simp [table4], by omega, minGB_le_of_small seg_20 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 3526958 with h21 | h21
  · exact ⟨(1077422, 601), by simp [table4], by omega, minGB_le_of_small seg_21 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 3807404 with h22 | h22
  · exact ⟨(3526958, 727), by simp [table4], by omega, minGB_le_of_small seg_22 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  exact ⟨(3807404, 751), by simp [table4], by omega, minGB_le_of_small seg_23 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩

end LeanLab.OeSHP2014.U1385

#print axioms LeanLab.OeSHP2014.U1385.table4_least
#print axioms LeanLab.OeSHP2014.U1385.table4_complete
