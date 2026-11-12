/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_0 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 0 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_1 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_2 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_3 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_4 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 4 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_5 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 5 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_6 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 6 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_7 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 7 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_8 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 8 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_9 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 9 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_10 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 10 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_11 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 11 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_12 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 12 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_13 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 13 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_14 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 14 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_15 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 15 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_16 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 16 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_17 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 17 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_18 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 18 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_19 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 19 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_20 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 20 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_21 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 21 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_22 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 22 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_23 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 23 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_24 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 24 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_25 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 25 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_26 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 26 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_27 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 27 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_28 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 28 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_29 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 29 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_30 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 30 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_31 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 31 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_32 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 32 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_33 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 33 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_34 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 34 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_35 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 35 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_36 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 36 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_37 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 37 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_38 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 38 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_39 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 39 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_40 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 40 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_41 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 41 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_42 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 42 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_43 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 43 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_44 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 44 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_45 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 45 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_46 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 46 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_47 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 47 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_48 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 48 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_49 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 49 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_50 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 50 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_51 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 51 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_52 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 52 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_53 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 53 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_54 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 54 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_55 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 55 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_56 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 56 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_57 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 57 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_58 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 58 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_59 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 59 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_60 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 60 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_61 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 61 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_62 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 62 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_63 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 63 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
/-- Page 51. Exact E2 row block 0 through 63. -/
theorem lowerTwo_rows312_00 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (0+i) j) = 0 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_0, lowerTwo_row_1, lowerTwo_row_2, lowerTwo_row_3, lowerTwo_row_4, lowerTwo_row_5, lowerTwo_row_6, lowerTwo_row_7, lowerTwo_row_8, lowerTwo_row_9, lowerTwo_row_10, lowerTwo_row_11, lowerTwo_row_12, lowerTwo_row_13, lowerTwo_row_14, lowerTwo_row_15, lowerTwo_row_16, lowerTwo_row_17, lowerTwo_row_18, lowerTwo_row_19, lowerTwo_row_20, lowerTwo_row_21, lowerTwo_row_22, lowerTwo_row_23, lowerTwo_row_24, lowerTwo_row_25, lowerTwo_row_26, lowerTwo_row_27, lowerTwo_row_28, lowerTwo_row_29, lowerTwo_row_30, lowerTwo_row_31, lowerTwo_row_32, lowerTwo_row_33, lowerTwo_row_34, lowerTwo_row_35, lowerTwo_row_36, lowerTwo_row_37, lowerTwo_row_38, lowerTwo_row_39, lowerTwo_row_40, lowerTwo_row_41, lowerTwo_row_42, lowerTwo_row_43, lowerTwo_row_44, lowerTwo_row_45, lowerTwo_row_46, lowerTwo_row_47, lowerTwo_row_48, lowerTwo_row_49, lowerTwo_row_50, lowerTwo_row_51, lowerTwo_row_52, lowerTwo_row_53, lowerTwo_row_54, lowerTwo_row_55, lowerTwo_row_56, lowerTwo_row_57, lowerTwo_row_58, lowerTwo_row_59, lowerTwo_row_60, lowerTwo_row_61, lowerTwo_row_62, lowerTwo_row_63, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
