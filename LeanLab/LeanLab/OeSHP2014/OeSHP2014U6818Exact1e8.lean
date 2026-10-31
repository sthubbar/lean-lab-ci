/-
U-6818, P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 4 made exact on [6, 10^8].
Extends OeSHP2014U6818Exact1e7.lean: for every Table 4 row with n ≤ 10^8, PROVED zero sorry,
every even m with 4 ≤ m < n has minGB m < p, so n is the least n with p(n) = p and the row
is a record; and every even m with 6 ≤ m ≤ 10^8 has minGB m ≤ p for some row (n, p) with
n ≤ m, so no record of p(n) below 10^8 is missing from Table 4. Above 10^7 each record gap
is covered by windows of at most 2000000, in OeSHP2014U6818Seg23 to Seg26 and Tail01 to Tail16, one bignum sieve equality each, wem and wpm of
Verifications/Top50/BitSieve.lean, small prime bounded by the row's p. Rows above 10^8 stay
cited. AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail16

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Leastness: below each Table 4 row with n ≤ 10^8, every even m has a smaller p(m). -/
theorem table4_least : ∀ x ∈ table4, x.1 ≤ 100000000 → ∀ m, Even m → 4 ≤ m → m < x.1 →
    minGB m < x.2 := by
  intro x hx
  simp only [table4, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_0 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_1 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_2 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_3 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_4 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_5 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_6 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_7 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_8 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_9 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_10 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_11 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_12 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_13 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_14 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_15 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_16 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_17 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_18 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_19 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_20 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_21 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small Exact1e7.seg_22 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_23 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_24 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_25 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_26 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
    omega
  · intro _ m hm h4 hlt
    have := minGB_le_of_small seg_27 hm h4 (by obtain ⟨r, hr⟩ := hm; omega)
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

/-- Completeness: every even m with 6 ≤ m ≤ 10^8 is bounded by a Table 4 row at or below m. -/
theorem table4_complete : ∀ m, Even m → 6 ≤ m → m ≤ 100000000 →
    ∃ x ∈ table4, x.1 ≤ m ∧ minGB m ≤ x.2 := by
  intro m hm h6 hmN
  rcases Nat.lt_or_ge m 12 with h1 | h1
  · exact ⟨(6, 3), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_1 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 30 with h2 | h2
  · exact ⟨(12, 5), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_2 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 98 with h3 | h3
  · exact ⟨(30, 7), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_3 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 220 with h4 | h4
  · exact ⟨(98, 19), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_4 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 308 with h5 | h5
  · exact ⟨(220, 23), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_5 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 556 with h6 | h6
  · exact ⟨(308, 31), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_6 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 992 with h7 | h7
  · exact ⟨(556, 47), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_7 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 2642 with h8 | h8
  · exact ⟨(992, 73), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_8 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 5372 with h9 | h9
  · exact ⟨(2642, 103), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_9 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 7426 with h10 | h10
  · exact ⟨(5372, 139), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_10 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 43532 with h11 | h11
  · exact ⟨(7426, 173), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_11 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 54244 with h12 | h12
  · exact ⟨(43532, 211), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_12 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 63274 with h13 | h13
  · exact ⟨(54244, 233), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_13 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 113672 with h14 | h14
  · exact ⟨(63274, 293), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_14 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 128168 with h15 | h15
  · exact ⟨(113672, 313), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_15 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 194428 with h16 | h16
  · exact ⟨(128168, 331), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_16 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 194470 with h17 | h17
  · exact ⟨(194428, 359), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_17 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 413572 with h18 | h18
  · exact ⟨(194470, 383), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_18 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 503222 with h19 | h19
  · exact ⟨(413572, 389), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_19 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 1077422 with h20 | h20
  · exact ⟨(503222, 523), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_20 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 3526958 with h21 | h21
  · exact ⟨(1077422, 601), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_21 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 3807404 with h22 | h22
  · exact ⟨(3526958, 727), by simp [table4], by omega, minGB_le_of_small Exact1e7.seg_22 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 10759922 with h23 | h23
  · exact ⟨(3807404, 751), by simp [table4], by omega, minGB_le_of_small seg_23 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 24106882 with h24 | h24
  · exact ⟨(10759922, 829), by simp [table4], by omega, minGB_le_of_small seg_24 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 27789878 with h25 | h25
  · exact ⟨(24106882, 929), by simp [table4], by omega, minGB_le_of_small seg_25 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 37998938 with h26 | h26
  · exact ⟨(27789878, 997), by simp [table4], by omega, minGB_le_of_small seg_26 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  rcases Nat.lt_or_ge m 60119912 with h27 | h27
  · exact ⟨(37998938, 1039), by simp [table4], by omega, minGB_le_of_small seg_27 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩
  exact ⟨(60119912, 1093), by simp [table4], by omega, minGB_le_of_small seg_28 hm (by omega) (by obtain ⟨r, hr⟩ := hm; omega)⟩

end LeanLab.OeSHP2014.Exact1e8

#print axioms LeanLab.OeSHP2014.Exact1e8.table4_least
#print axioms LeanLab.OeSHP2014.Exact1e8.table4_complete
