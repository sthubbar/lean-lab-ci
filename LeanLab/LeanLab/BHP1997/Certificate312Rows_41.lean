/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2624 j) = 346035859 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2625 j) = 346448378 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2626 j) = 345114106 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2627 j) = 345207700 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2628 j) = 345892018 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2629 j) = 345165275 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2630 j) = 345530857 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2631 j) = 345056277 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2632 j) = 344596789 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2633 j) = 344689522 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2634 j) = 345374649 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2635 j) = 344639505 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2636 j) = 344112530 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2637 j) = 344525575 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2638 j) = 344057596 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2639 j) = 344149375 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2640 j) = 344835333 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2641 j) = 343195968 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2642 j) = 343558779 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2643 j) = 343972575 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2644 j) = 343495935 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2645 j) = 343586743 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2646 j) = 343374009 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2647 j) = 342620360 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2648 j) = 342982255 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2649 j) = 343396707 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2650 j) = 342911244 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2651 j) = 342097674 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2652 j) = 342784076 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2653 j) = 342021437 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2654 j) = 342382328 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2655 j) = 342797434 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2656 j) = 341395611 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2657 j) = 341483310 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2658 j) = 342170384 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2659 j) = 341398588 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2660 j) = 341758440 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2661 j) = 341262801 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2662 j) = 340758121 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2663 j) = 340844605 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2664 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2664 j) = 341532311 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2665 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2665 j) = 340751197 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2666 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2666 j) = 340194606 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2667 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2667 j) = 340609776 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2668 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2668 j) = 340095705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2669 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2669 j) = 340181020 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2670 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2670 j) = 340869339 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2671 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2671 j) = 339159271 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2672 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2672 j) = 339515787 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2673 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2673 j) = 339931473 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2674 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2674 j) = 339407818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2675 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2675 j) = 339491822 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2676 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2676 j) = 339257246 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2677 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2677 j) = 338455758 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2678 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2678 j) = 338811004 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2679 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2679 j) = 339227200 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2680 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2680 j) = 338693767 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2681 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2681 j) = 337848846 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2682 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2682 j) = 338537188 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2683 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2683 j) = 337725728 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2684 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2684 j) = 338079732 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2685 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2685 j) = 338496315 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2686 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2686 j) = 337021124 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2687 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2687 j) = 337101349 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2624 through 2687. -/
theorem lowerTwo_rows312_41 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2624+i) j) = 21882676110 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2624, lowerTwo_row_2625, lowerTwo_row_2626, lowerTwo_row_2627, lowerTwo_row_2628, lowerTwo_row_2629, lowerTwo_row_2630, lowerTwo_row_2631, lowerTwo_row_2632, lowerTwo_row_2633, lowerTwo_row_2634, lowerTwo_row_2635, lowerTwo_row_2636, lowerTwo_row_2637, lowerTwo_row_2638, lowerTwo_row_2639, lowerTwo_row_2640, lowerTwo_row_2641, lowerTwo_row_2642, lowerTwo_row_2643, lowerTwo_row_2644, lowerTwo_row_2645, lowerTwo_row_2646, lowerTwo_row_2647, lowerTwo_row_2648, lowerTwo_row_2649, lowerTwo_row_2650, lowerTwo_row_2651, lowerTwo_row_2652, lowerTwo_row_2653, lowerTwo_row_2654, lowerTwo_row_2655, lowerTwo_row_2656, lowerTwo_row_2657, lowerTwo_row_2658, lowerTwo_row_2659, lowerTwo_row_2660, lowerTwo_row_2661, lowerTwo_row_2662, lowerTwo_row_2663, lowerTwo_row_2664, lowerTwo_row_2665, lowerTwo_row_2666, lowerTwo_row_2667, lowerTwo_row_2668, lowerTwo_row_2669, lowerTwo_row_2670, lowerTwo_row_2671, lowerTwo_row_2672, lowerTwo_row_2673, lowerTwo_row_2674, lowerTwo_row_2675, lowerTwo_row_2676, lowerTwo_row_2677, lowerTwo_row_2678, lowerTwo_row_2679, lowerTwo_row_2680, lowerTwo_row_2681, lowerTwo_row_2682, lowerTwo_row_2683, lowerTwo_row_2684, lowerTwo_row_2685, lowerTwo_row_2686, lowerTwo_row_2687, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
