/-
U-6818, P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 4 made exact on [6, 10000000].
Table 4 lists the n where p(n), the least prime p with n - p prime, beats every earlier value.
The earlier unit U-0946 PROVED minGB n = p on all 68 rows; leastness and completeness of the
record list were cited. Here, for every row with n ≤ 10000000, PROVED zero sorry: every even m
with 4 ≤ m < n has minGB m < p, so n is the least n with p(n) = p and the row is a record;
and every even m with 6 ≤ m ≤ 10000000 has minGB m ≤ p for some row (n, p) with n ≤ m, so no
record below 10000000 is missing. One bignum sieve check per gap between rows, the BitSieve
machinery of Verifications/Top50, small prime bounded by the row's p.
The rows above 10000000 stay cited. AI-written Lean code, Claude, 2026-10-21,
run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.Tables
import LeanLab.Verifications.Top50.SmallGB

namespace LeanLab.OeSHP2014.Exact1e7

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- One sieve check gives a bounded small prime on the whole range from 4. -/
theorem small_of_check {N B L k : ℕ} (hL : L ≤ 10 ^ 8) (hk : ∀ q ∈ P10k.take k, q ≤ N)
    (h : em 4 B &&& gm (pm L) (P10k.take k) = em 4 B) : SmallGBUpTo N B := by
  intro n hn h4 hnB
  have he : 2 ∣ n - 4 := by obtain ⟨j, rfl⟩ := hn; exact ⟨j - 2, by omega⟩
  have h1 := testBit_em h4 hnB he
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at h1
  obtain ⟨q, hq, hqn, hp⟩ := of_gm _ _ n h1.2
  exact ⟨q, take_prime k q hq, hk q hq, hqn, prime_of_pm hL hp⟩

theorem take_le_0 : ∀ q ∈ P10k.take 1, q ≤ 2 := by
  have h : (P10k.take 1).all (fun q => decide (q ≤ 2)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_0 : em 4 4 &&& gm (pm 5) (P10k.take 1) = em 4 4 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 4 has minGB m ≤ 2. -/
theorem seg_0 : SmallGBUpTo 2 4 := small_of_check (by norm_num) take_le_0 check_0

theorem take_le_1 : ∀ q ∈ P10k.take 2, q ≤ 3 := by
  have h : (P10k.take 2).all (fun q => decide (q ≤ 3)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_1 : em 4 10 &&& gm (pm 11) (P10k.take 2) = em 4 10 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 10 has minGB m ≤ 3. -/
theorem seg_1 : SmallGBUpTo 3 10 := small_of_check (by norm_num) take_le_1 check_1

theorem take_le_2 : ∀ q ∈ P10k.take 3, q ≤ 5 := by
  have h : (P10k.take 3).all (fun q => decide (q ≤ 5)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_2 : em 4 28 &&& gm (pm 29) (P10k.take 3) = em 4 28 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 28 has minGB m ≤ 5. -/
theorem seg_2 : SmallGBUpTo 5 28 := small_of_check (by norm_num) take_le_2 check_2

theorem take_le_3 : ∀ q ∈ P10k.take 4, q ≤ 7 := by
  have h : (P10k.take 4).all (fun q => decide (q ≤ 7)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_3 : em 4 96 &&& gm (pm 97) (P10k.take 4) = em 4 96 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 96 has minGB m ≤ 7. -/
theorem seg_3 : SmallGBUpTo 7 96 := small_of_check (by norm_num) take_le_3 check_3

theorem take_le_4 : ∀ q ∈ P10k.take 8, q ≤ 19 := by
  have h : (P10k.take 8).all (fun q => decide (q ≤ 19)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_4 : em 4 218 &&& gm (pm 219) (P10k.take 8) = em 4 218 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 218 has minGB m ≤ 19. -/
theorem seg_4 : SmallGBUpTo 19 218 := small_of_check (by norm_num) take_le_4 check_4

theorem take_le_5 : ∀ q ∈ P10k.take 9, q ≤ 23 := by
  have h : (P10k.take 9).all (fun q => decide (q ≤ 23)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_5 : em 4 306 &&& gm (pm 307) (P10k.take 9) = em 4 306 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 306 has minGB m ≤ 23. -/
theorem seg_5 : SmallGBUpTo 23 306 := small_of_check (by norm_num) take_le_5 check_5

theorem take_le_6 : ∀ q ∈ P10k.take 11, q ≤ 31 := by
  have h : (P10k.take 11).all (fun q => decide (q ≤ 31)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_6 : em 4 554 &&& gm (pm 555) (P10k.take 11) = em 4 554 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 554 has minGB m ≤ 31. -/
theorem seg_6 : SmallGBUpTo 31 554 := small_of_check (by norm_num) take_le_6 check_6

theorem take_le_7 : ∀ q ∈ P10k.take 15, q ≤ 47 := by
  have h : (P10k.take 15).all (fun q => decide (q ≤ 47)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_7 : em 4 990 &&& gm (pm 991) (P10k.take 15) = em 4 990 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 990 has minGB m ≤ 47. -/
theorem seg_7 : SmallGBUpTo 47 990 := small_of_check (by norm_num) take_le_7 check_7

theorem take_le_8 : ∀ q ∈ P10k.take 21, q ≤ 73 := by
  have h : (P10k.take 21).all (fun q => decide (q ≤ 73)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_8 : em 4 2640 &&& gm (pm 2641) (P10k.take 21) = em 4 2640 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 2640 has minGB m ≤ 73. -/
theorem seg_8 : SmallGBUpTo 73 2640 := small_of_check (by norm_num) take_le_8 check_8

theorem take_le_9 : ∀ q ∈ P10k.take 27, q ≤ 103 := by
  have h : (P10k.take 27).all (fun q => decide (q ≤ 103)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_9 : em 4 5370 &&& gm (pm 5371) (P10k.take 27) = em 4 5370 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 5370 has minGB m ≤ 103. -/
theorem seg_9 : SmallGBUpTo 103 5370 := small_of_check (by norm_num) take_le_9 check_9

theorem take_le_10 : ∀ q ∈ P10k.take 34, q ≤ 139 := by
  have h : (P10k.take 34).all (fun q => decide (q ≤ 139)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_10 : em 4 7424 &&& gm (pm 7425) (P10k.take 34) = em 4 7424 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 7424 has minGB m ≤ 139. -/
theorem seg_10 : SmallGBUpTo 139 7424 := small_of_check (by norm_num) take_le_10 check_10

theorem take_le_11 : ∀ q ∈ P10k.take 40, q ≤ 173 := by
  have h : (P10k.take 40).all (fun q => decide (q ≤ 173)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_11 : em 4 43530 &&& gm (pm 43531) (P10k.take 40) = em 4 43530 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 43530 has minGB m ≤ 173. -/
theorem seg_11 : SmallGBUpTo 173 43530 := small_of_check (by norm_num) take_le_11 check_11

theorem take_le_12 : ∀ q ∈ P10k.take 47, q ≤ 211 := by
  have h : (P10k.take 47).all (fun q => decide (q ≤ 211)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_12 : em 4 54242 &&& gm (pm 54243) (P10k.take 47) = em 4 54242 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 54242 has minGB m ≤ 211. -/
theorem seg_12 : SmallGBUpTo 211 54242 := small_of_check (by norm_num) take_le_12 check_12

theorem take_le_13 : ∀ q ∈ P10k.take 51, q ≤ 233 := by
  have h : (P10k.take 51).all (fun q => decide (q ≤ 233)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_13 : em 4 63272 &&& gm (pm 63273) (P10k.take 51) = em 4 63272 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 63272 has minGB m ≤ 233. -/
theorem seg_13 : SmallGBUpTo 233 63272 := small_of_check (by norm_num) take_le_13 check_13

theorem take_le_14 : ∀ q ∈ P10k.take 62, q ≤ 293 := by
  have h : (P10k.take 62).all (fun q => decide (q ≤ 293)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_14 : em 4 113670 &&& gm (pm 113671) (P10k.take 62) = em 4 113670 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 113670 has minGB m ≤ 293. -/
theorem seg_14 : SmallGBUpTo 293 113670 := small_of_check (by norm_num) take_le_14 check_14

theorem take_le_15 : ∀ q ∈ P10k.take 65, q ≤ 313 := by
  have h : (P10k.take 65).all (fun q => decide (q ≤ 313)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_15 : em 4 128166 &&& gm (pm 128167) (P10k.take 65) = em 4 128166 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 128166 has minGB m ≤ 313. -/
theorem seg_15 : SmallGBUpTo 313 128166 := small_of_check (by norm_num) take_le_15 check_15

theorem take_le_16 : ∀ q ∈ P10k.take 67, q ≤ 331 := by
  have h : (P10k.take 67).all (fun q => decide (q ≤ 331)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_16 : em 4 194426 &&& gm (pm 194427) (P10k.take 67) = em 4 194426 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 194426 has minGB m ≤ 331. -/
theorem seg_16 : SmallGBUpTo 331 194426 := small_of_check (by norm_num) take_le_16 check_16

theorem take_le_17 : ∀ q ∈ P10k.take 72, q ≤ 359 := by
  have h : (P10k.take 72).all (fun q => decide (q ≤ 359)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_17 : em 4 194468 &&& gm (pm 194469) (P10k.take 72) = em 4 194468 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 194468 has minGB m ≤ 359. -/
theorem seg_17 : SmallGBUpTo 359 194468 := small_of_check (by norm_num) take_le_17 check_17

theorem take_le_18 : ∀ q ∈ P10k.take 76, q ≤ 383 := by
  have h : (P10k.take 76).all (fun q => decide (q ≤ 383)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_18 : em 4 413570 &&& gm (pm 413571) (P10k.take 76) = em 4 413570 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 413570 has minGB m ≤ 383. -/
theorem seg_18 : SmallGBUpTo 383 413570 := small_of_check (by norm_num) take_le_18 check_18

theorem take_le_19 : ∀ q ∈ P10k.take 77, q ≤ 389 := by
  have h : (P10k.take 77).all (fun q => decide (q ≤ 389)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_19 : em 4 503220 &&& gm (pm 503221) (P10k.take 77) = em 4 503220 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 503220 has minGB m ≤ 389. -/
theorem seg_19 : SmallGBUpTo 389 503220 := small_of_check (by norm_num) take_le_19 check_19

theorem take_le_20 : ∀ q ∈ P10k.take 99, q ≤ 523 := by
  have h : (P10k.take 99).all (fun q => decide (q ≤ 523)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_20 : em 4 1077420 &&& gm (pm 1077421) (P10k.take 99) = em 4 1077420 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 1077420 has minGB m ≤ 523. -/
theorem seg_20 : SmallGBUpTo 523 1077420 := small_of_check (by norm_num) take_le_20 check_20

theorem take_le_21 : ∀ q ∈ P10k.take 110, q ≤ 601 := by
  have h : (P10k.take 110).all (fun q => decide (q ≤ 601)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_21 : em 4 3526956 &&& gm (pm 3526957) (P10k.take 110) = em 4 3526956 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 3526956 has minGB m ≤ 601. -/
theorem seg_21 : SmallGBUpTo 601 3526956 := small_of_check (by norm_num) take_le_21 check_21

theorem take_le_22 : ∀ q ∈ P10k.take 129, q ≤ 727 := by
  have h : (P10k.take 129).all (fun q => decide (q ≤ 727)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_22 : em 4 3807402 &&& gm (pm 3807403) (P10k.take 129) = em 4 3807402 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 3807402 has minGB m ≤ 727. -/
theorem seg_22 : SmallGBUpTo 727 3807402 := small_of_check (by norm_num) take_le_22 check_22

theorem take_le_23 : ∀ q ∈ P10k.take 133, q ≤ 751 := by
  have h : (P10k.take 133).all (fun q => decide (q ≤ 751)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_23 : em 4 10000000 &&& gm (pm 10000001) (P10k.take 133) = em 4 10000000 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 10000000 has minGB m ≤ 751. -/
theorem seg_23 : SmallGBUpTo 751 10000000 := small_of_check (by norm_num) take_le_23 check_23

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

end LeanLab.OeSHP2014.Exact1e7

#print axioms LeanLab.OeSHP2014.Exact1e7.table4_least
#print axioms LeanLab.OeSHP2014.Exact1e7.table4_complete
