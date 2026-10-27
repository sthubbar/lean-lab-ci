/-
U-1385, run PC 20261021T0803Z-19426. Part 1 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
Holds small_of_check and the windows 0 to 20, up to 1077420.
Same checks as the original, verbatim; only the file layout changed so that each kernel
sieve check runs in its own module, elaborated sequentially.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.Tables
import LeanLab.Verifications.Top50.SmallGB

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

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

end LeanLab.OeSHP2014.U1385
