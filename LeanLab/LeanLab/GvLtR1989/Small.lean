/-
P0042 GvLtR 1989 ratio check, even n from 6 to 10^6 in 12 blocks of the full bitmap.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_0 : em 6 6 &&& gm (pm 7) (P10k.take 2) = em 6 6 := by
  decide +kernel

theorem bnd_0 : MinGBBound 6 6 3 :=
  bound_of_check (by norm_num) (by decide) (take_le 2 3 (by decide)) chk_0

theorem lr_0 : (1 + 7917593/10000000 : ℝ) ≤ Real.log ((6 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((6 : ℕ) : ℝ)) 1 (f := (7917593/10000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_0 : (0 + 2915989/5000000 : ℝ) ≤ Real.log (1 + 7917593/10000000 : ℝ) := by
  have h := le_log_of (x := (1 + 7917593/10000000 : ℝ)) 0 (f := (2915989/5000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_0 : ∀ n, Even n → 6 ≤ n → n ≤ 6 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_0 ls_0 (by norm_num) (by norm_num) bnd_0

theorem chk_1 : em 8 8 &&& gm (pm 9) (P10k.take 2) = em 8 8 := by
  decide +kernel

theorem bnd_1 : MinGBBound 8 8 3 :=
  bound_of_check (by norm_num) (by decide) (take_le 2 3 (by decide)) chk_1

theorem lr_1 : (2 + 993/12500 : ℝ) ≤ Real.log ((8 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((8 : ℕ) : ℝ)) 2 (f := (993/12500 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_1 : (0 + 732097/1000000 : ℝ) ≤ Real.log (2 + 993/12500 : ℝ) := by
  have h := le_log_of (x := (2 + 993/12500 : ℝ)) 0 (f := (732097/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_1 : ∀ n, Even n → 8 ≤ n → n ≤ 8 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_1 ls_1 (by norm_num) (by norm_num) bnd_1

theorem r2_1 : ∀ n, Even n → 8 ≤ n → n ≤ 8 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_1 ls_1 (by norm_num) (by norm_num) bnd_1

theorem chk_2 : em 10 28 &&& gm (pm 29) (P10k.take 3) = em 10 28 := by
  decide +kernel

theorem bnd_2 : MinGBBound 10 28 5 :=
  bound_of_check (by norm_num) (by decide) (take_le 3 5 (by decide)) chk_2

theorem lr_2 : (2 + 37823/125000 : ℝ) ≤ Real.log ((10 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((10 : ℕ) : ℝ)) 2 (f := (37823/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_2 : (0 + 83403/100000 : ℝ) ≤ Real.log (2 + 37823/125000 : ℝ) := by
  have h := le_log_of (x := (2 + 37823/125000 : ℝ)) 0 (f := (83403/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_2 : ∀ n, Even n → 10 ≤ n → n ≤ 28 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_2 ls_2 (by norm_num) (by norm_num) bnd_2

theorem r2_2 : ∀ n, Even n → 10 ≤ n → n ≤ 28 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_2 ls_2 (by norm_num) (by norm_num) bnd_2

theorem chk_3 : em 30 96 &&& gm (pm 97) (P10k.take 4) = em 30 96 := by
  decide +kernel

theorem bnd_3 : MinGBBound 30 96 7 :=
  bound_of_check (by norm_num) (by decide) (take_le 4 7 (by decide)) chk_3

theorem lr_3 : (3 + 100299/250000 : ℝ) ≤ Real.log ((30 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((30 : ℕ) : ℝ)) 3 (f := (100299/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_3 : (1 + 112063/500000 : ℝ) ≤ Real.log (3 + 100299/250000 : ℝ) := by
  have h := le_log_of (x := (3 + 100299/250000 : ℝ)) 1 (f := (112063/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_3 : ∀ n, Even n → 30 ≤ n → n ≤ 96 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_3 ls_3 (by norm_num) (by norm_num) bnd_3

theorem r2_3 : ∀ n, Even n → 30 ≤ n → n ≤ 96 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_3 ls_3 (by norm_num) (by norm_num) bnd_3

theorem chk_4 : em 98 552 &&& gm (pm 553) (P10k.take 11) = em 98 552 := by
  decide +kernel

theorem bnd_4 : MinGBBound 98 552 31 :=
  bound_of_check (by norm_num) (by decide) (take_le 11 31 (by decide)) chk_4

theorem lr_4 : (4 + 292483/500000 : ℝ) ≤ Real.log ((98 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((98 : ℕ) : ℝ)) 4 (f := (292483/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_4 : (1 + 522781/1000000 : ℝ) ≤ Real.log (4 + 292483/500000 : ℝ) := by
  have h := le_log_of (x := (4 + 292483/500000 : ℝ)) 1 (f := (522781/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_4 : ∀ n, Even n → 98 ≤ n → n ≤ 552 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_4 ls_4 (by norm_num) (by norm_num) bnd_4

theorem r2_4 : ∀ n, Even n → 98 ≤ n → n ≤ 552 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_4 ls_4 (by norm_num) (by norm_num) bnd_4

theorem chk_5 : em 554 2638 &&& gm (pm 2639) (P10k.take 21) = em 554 2638 := by
  decide +kernel

theorem bnd_5 : MinGBBound 554 2638 73 :=
  bound_of_check (by norm_num) (by decide) (take_le 21 73 (by decide)) chk_5

theorem lr_5 : (6 + 317163/1000000 : ℝ) ≤ Real.log ((554 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((554 : ℕ) : ℝ)) 6 (f := (317163/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_5 : (1 + 843269/1000000 : ℝ) ≤ Real.log (6 + 317163/1000000 : ℝ) := by
  have h := le_log_of (x := (6 + 317163/1000000 : ℝ)) 1 (f := (843269/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_5 : ∀ n, Even n → 554 ≤ n → n ≤ 2638 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_5 ls_5 (by norm_num) (by norm_num) bnd_5

theorem r2_5 : ∀ n, Even n → 554 ≤ n → n ≤ 2638 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_5 ls_5 (by norm_num) (by norm_num) bnd_5

theorem chk_6 : em 2640 7424 &&& gm (pm 7425) (P10k.take 34) = em 2640 7424 := by
  decide +kernel

theorem bnd_6 : MinGBBound 2640 7424 139 :=
  bound_of_check (by norm_num) (by decide) (take_le 34 139 (by decide)) chk_6

theorem lr_6 : (7 + 878533/1000000 : ℝ) ≤ Real.log ((2640 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((2640 : ℕ) : ℝ)) 7 (f := (878533/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_6 : (2 + 3207/50000 : ℝ) ≤ Real.log (7 + 878533/1000000 : ℝ) := by
  have h := le_log_of (x := (7 + 878533/1000000 : ℝ)) 2 (f := (3207/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_6 : ∀ n, Even n → 2640 ≤ n → n ≤ 7424 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_6 ls_6 (by norm_num) (by norm_num) bnd_6

theorem r2_6 : ∀ n, Even n → 2640 ≤ n → n ≤ 7424 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_6 ls_6 (by norm_num) (by norm_num) bnd_6

theorem chk_7 : em 7426 54242 &&& gm (pm 54243) (P10k.take 47) = em 7426 54242 := by
  decide +kernel

theorem bnd_7 : MinGBBound 7426 54242 211 :=
  bound_of_check (by norm_num) (by decide) (take_le 47 211 (by decide)) chk_7

theorem lr_7 : (8 + 912741/1000000 : ℝ) ≤ Real.log ((7426 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((7426 : ℕ) : ℝ)) 8 (f := (912741/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_7 : (2 + 4687/25000 : ℝ) ≤ Real.log (8 + 912741/1000000 : ℝ) := by
  have h := le_log_of (x := (8 + 912741/1000000 : ℝ)) 2 (f := (4687/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_7 : ∀ n, Even n → 7426 ≤ n → n ≤ 54242 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_7 ls_7 (by norm_num) (by norm_num) bnd_7

theorem r2_7 : ∀ n, Even n → 7426 ≤ n → n ≤ 54242 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_7 ls_7 (by norm_num) (by norm_num) bnd_7

theorem chk_8 : em 54244 194426 &&& gm (pm 194427) (P10k.take 67) = em 54244 194426 := by
  decide +kernel

theorem bnd_8 : MinGBBound 54244 194426 331 :=
  bound_of_check (by norm_num) (by decide) (take_le 67 331 (by decide)) chk_8

theorem lr_8 : (10 + 450623/500000 : ℝ) ≤ Real.log ((54244 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((54244 : ℕ) : ℝ)) 10 (f := (450623/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_8 : (2 + 97219/250000 : ℝ) ≤ Real.log (10 + 450623/500000 : ℝ) := by
  have h := le_log_of (x := (10 + 450623/500000 : ℝ)) 2 (f := (97219/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_8 : ∀ n, Even n → 54244 ≤ n → n ≤ 194426 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_8 ls_8 (by norm_num) (by norm_num) bnd_8

theorem r2_8 : ∀ n, Even n → 54244 ≤ n → n ≤ 194426 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_8 ls_8 (by norm_num) (by norm_num) bnd_8

theorem chk_9 : em 194428 503218 &&& gm (pm 503219) (P10k.take 77) = em 194428 503218 := by
  decide +kernel

theorem bnd_9 : MinGBBound 194428 503218 389 :=
  bound_of_check (by norm_num) (by decide) (take_le 77 389 (by decide)) chk_9

theorem lr_9 : (12 + 22227/125000 : ℝ) ≤ Real.log ((194428 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((194428 : ℕ) : ℝ)) 12 (f := (22227/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_9 : (2 + 249807/500000 : ℝ) ≤ Real.log (12 + 22227/125000 : ℝ) := by
  have h := le_log_of (x := (12 + 22227/125000 : ℝ)) 2 (f := (249807/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_9 : ∀ n, Even n → 194428 ≤ n → n ≤ 503218 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_9 ls_9 (by norm_num) (by norm_num) bnd_9

theorem r2_9 : ∀ n, Even n → 194428 ≤ n → n ≤ 503218 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_9 ls_9 (by norm_num) (by norm_num) bnd_9

theorem chk_10 : em 503220 999998 &&& gm (pm 999999) (P10k.take 99) = em 503220 999998 := by
  decide +kernel

theorem bnd_10 : MinGBBound 503220 999998 523 :=
  bound_of_check (by norm_num) (by decide) (take_le 99 523 (by decide)) chk_10

theorem lr_10 : (13 + 128781/1000000 : ℝ) ≤ Real.log ((503220 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((503220 : ℕ) : ℝ)) 13 (f := (128781/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_10 : (2 + 114961/200000 : ℝ) ≤ Real.log (13 + 128781/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 128781/1000000 : ℝ)) 2 (f := (114961/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_10 : ∀ n, Even n → 503220 ≤ n → n ≤ 999998 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_10 ls_10 (by norm_num) (by norm_num) bnd_10

theorem r2_10 : ∀ n, Even n → 503220 ≤ n → n ≤ 999998 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_10 ls_10 (by norm_num) (by norm_num) bnd_10

theorem chk_11 : em 1000000 1000000 &&& gm (pm 1000001) (P10k.take 7) = em 1000000 1000000 := by
  decide +kernel

theorem bnd_11 : MinGBBound 1000000 1000000 17 :=
  bound_of_check (by norm_num) (by decide) (take_le 7 17 (by decide)) chk_11

theorem lr_11 : (13 + 815509/1000000 : ℝ) ≤ Real.log ((1000000 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((1000000 : ℕ) : ℝ)) 13 (f := (815509/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_11 : (2 + 62579/100000 : ℝ) ≤ Real.log (13 + 815509/1000000 : ℝ) := by
  have h := le_log_of (x := (13 + 815509/1000000 : ℝ)) 2 (f := (62579/100000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_11 : ∀ n, Even n → 1000000 ≤ n → n ≤ 1000000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_11 ls_11 (by norm_num) (by norm_num) bnd_11

theorem r2_11 : ∀ n, Even n → 1000000 ≤ n → n ≤ 1000000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_11 ls_11 (by norm_num) (by norm_num) bnd_11

end LeanLab.GvLtR1989
