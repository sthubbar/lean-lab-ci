/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2688 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2688 j) = 337790147 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2689 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2689 j) = 336968533 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2690 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2690 j) = 337321190 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2691 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2691 j) = 336802173 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2692 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2692 j) = 336247446 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2693 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2693 j) = 336326239 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2694 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2694 j) = 337015451 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2695 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2695 j) = 336183480 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2696 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2696 j) = 335594492 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2697 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2697 j) = 336010667 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2698 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2698 j) = 335445557 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2699 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2699 j) = 335522792 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2700 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2700 j) = 336212363 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2701 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2701 j) = 334425346 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2702 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2702 j) = 334773952 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2703 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2703 j) = 335190386 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2704 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2704 j) = 334614673 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2705 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2705 j) = 334690274 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2706 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2706 j) = 334431441 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2707 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2707 j) = 333576939 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2708 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2708 j) = 333923961 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2709 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2709 j) = 334340639 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2710 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2710 j) = 333754049 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2711 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2711 j) = 332874869 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2712 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2712 j) = 333563926 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2713 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2713 j) = 332698396 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2714 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2714 j) = 333043752 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2715 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2715 j) = 333460618 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2716 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2716 j) = 331905470 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2717 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2717 j) = 331976502 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2718 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2718 j) = 332665758 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2719 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2719 j) = 331788925 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2720 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2720 j) = 332132613 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2721 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2721 j) = 331587657 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2722 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2722 j) = 330977506 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2723 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2723 j) = 331046712 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2724 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2724 j) = 331736139 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2725 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2725 j) = 330847758 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2726 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2726 j) = 330223322 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2727 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2727 j) = 330639125 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2728 j) = 330017413 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2729 j) = 330084717 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2730 j) = 329763548 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2731 j) = 327892938 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2732 j) = 328189774 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2733 j) = 328523080 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2734 j) = 328861798 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2735 j) = 328886583 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2736 j) = 329495650 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2737 j) = 329562336 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2738 j) = 329861440 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2739 j) = 330199904 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2740 j) = 330540940 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2741 j) = 330567955 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2742 j) = 331182267 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2743 j) = 331251187 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2744 j) = 331552573 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2745 j) = 331896291 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2746 j) = 332239632 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2747 j) = 332268864 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2748 j) = 332888575 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2749 j) = 332959698 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2750 j) = 333263417 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2751 j) = 333612438 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2688 through 2751. -/
theorem lowerTwo_rows312_42 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2688+i) j) = 21295894256 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2688, lowerTwo_row_2689, lowerTwo_row_2690, lowerTwo_row_2691, lowerTwo_row_2692, lowerTwo_row_2693, lowerTwo_row_2694, lowerTwo_row_2695, lowerTwo_row_2696, lowerTwo_row_2697, lowerTwo_row_2698, lowerTwo_row_2699, lowerTwo_row_2700, lowerTwo_row_2701, lowerTwo_row_2702, lowerTwo_row_2703, lowerTwo_row_2704, lowerTwo_row_2705, lowerTwo_row_2706, lowerTwo_row_2707, lowerTwo_row_2708, lowerTwo_row_2709, lowerTwo_row_2710, lowerTwo_row_2711, lowerTwo_row_2712, lowerTwo_row_2713, lowerTwo_row_2714, lowerTwo_row_2715, lowerTwo_row_2716, lowerTwo_row_2717, lowerTwo_row_2718, lowerTwo_row_2719, lowerTwo_row_2720, lowerTwo_row_2721, lowerTwo_row_2722, lowerTwo_row_2723, lowerTwo_row_2724, lowerTwo_row_2725, lowerTwo_row_2726, lowerTwo_row_2727, lowerTwo_row_2728, lowerTwo_row_2729, lowerTwo_row_2730, lowerTwo_row_2731, lowerTwo_row_2732, lowerTwo_row_2733, lowerTwo_row_2734, lowerTwo_row_2735, lowerTwo_row_2736, lowerTwo_row_2737, lowerTwo_row_2738, lowerTwo_row_2739, lowerTwo_row_2740, lowerTwo_row_2741, lowerTwo_row_2742, lowerTwo_row_2743, lowerTwo_row_2744, lowerTwo_row_2745, lowerTwo_row_2746, lowerTwo_row_2747, lowerTwo_row_2748, lowerTwo_row_2749, lowerTwo_row_2750, lowerTwo_row_2751, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
