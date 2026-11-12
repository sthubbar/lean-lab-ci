/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 704 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 705 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 706 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 707 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 708 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 709 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 710 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 711 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 712 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 713 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 714 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 715 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 716 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 717 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 718 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 719 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 720 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 721 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 722 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 723 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 724 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 725 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 726 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 727 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 728 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 729 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 730 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 731 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 732 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 733 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 734 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 735 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 736 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 737 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 738 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 739 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 740 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 741 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 742 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 743 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 744 j) = 1574430 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 745 j) = 2359408 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 746 j) = 3930489 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 747 j) = 5500085 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 748 j) = 6279866 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 749 j) = 7846137 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 750 j) = 8622594 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 751 j) = 10185549 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 752 j) = 10958697 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 753 j) = 12518357 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 754 j) = 14076557 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 755 j) = 14844581 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 756 j) = 16399510 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 757 j) = 17164253 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 758 j) = 18715918 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 759 j) = 19477406 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 760 j) = 21025818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 761 j) = 22572808 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 762 j) = 23329240 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 763 j) = 24873003 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 764 j) = 25626200 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 765 j) = 27166752 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 766 j) = 27916743 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 767 j) = 29454091 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 704 through 767. -/
theorem lowerTwo_rows312_11 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (704+i) j) = 372418492 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_704, lowerTwo_row_705, lowerTwo_row_706, lowerTwo_row_707, lowerTwo_row_708, lowerTwo_row_709, lowerTwo_row_710, lowerTwo_row_711, lowerTwo_row_712, lowerTwo_row_713, lowerTwo_row_714, lowerTwo_row_715, lowerTwo_row_716, lowerTwo_row_717, lowerTwo_row_718, lowerTwo_row_719, lowerTwo_row_720, lowerTwo_row_721, lowerTwo_row_722, lowerTwo_row_723, lowerTwo_row_724, lowerTwo_row_725, lowerTwo_row_726, lowerTwo_row_727, lowerTwo_row_728, lowerTwo_row_729, lowerTwo_row_730, lowerTwo_row_731, lowerTwo_row_732, lowerTwo_row_733, lowerTwo_row_734, lowerTwo_row_735, lowerTwo_row_736, lowerTwo_row_737, lowerTwo_row_738, lowerTwo_row_739, lowerTwo_row_740, lowerTwo_row_741, lowerTwo_row_742, lowerTwo_row_743, lowerTwo_row_744, lowerTwo_row_745, lowerTwo_row_746, lowerTwo_row_747, lowerTwo_row_748, lowerTwo_row_749, lowerTwo_row_750, lowerTwo_row_751, lowerTwo_row_752, lowerTwo_row_753, lowerTwo_row_754, lowerTwo_row_755, lowerTwo_row_756, lowerTwo_row_757, lowerTwo_row_758, lowerTwo_row_759, lowerTwo_row_760, lowerTwo_row_761, lowerTwo_row_762, lowerTwo_row_763, lowerTwo_row_764, lowerTwo_row_765, lowerTwo_row_766, lowerTwo_row_767, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
