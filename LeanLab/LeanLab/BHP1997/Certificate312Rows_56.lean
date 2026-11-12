/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3584 j) = 150955622 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3585 j) = 150676441 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3586 j) = 150692520 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3587 j) = 150413295 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3588 j) = 150429376 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3589 j) = 150150048 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3590 j) = 150166145 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3591 j) = 149886754 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3592 j) = 149902852 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3593 j) = 149623400 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3594 j) = 149639492 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3595 j) = 149359949 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3596 j) = 149376059 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3597 j) = 149096451 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3598 j) = 149112557 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3599 j) = 148832867 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3600 j) = 148848980 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3601 j) = 148569222 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3602 j) = 148585340 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3603 j) = 148305513 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3604 j) = 148321625 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3605 j) = 148041720 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3606 j) = 148057851 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3607 j) = 147777866 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3608 j) = 147793979 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3609 j) = 147513934 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3610 j) = 147530071 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3611 j) = 147249929 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3612 j) = 147266060 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3613 j) = 146985860 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3614 j) = 147001990 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3615 j) = 146721695 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3616 j) = 146737863 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3617 j) = 146457474 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3618 j) = 146473634 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3619 j) = 146193180 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3620 j) = 146209332 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3621 j) = 145928818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3622 j) = 145944974 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3623 j) = 145664357 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3624 j) = 145680522 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3625 j) = 145399856 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3626 j) = 145416008 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3627 j) = 145135253 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3628 j) = 145151419 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3629 j) = 144870576 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3630 j) = 144886761 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3631 j) = 144605837 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3632 j) = 144622003 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3633 j) = 144341011 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3634 j) = 144357191 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3635 j) = 144076127 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3636 j) = 144092297 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3637 j) = 143811135 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3638 j) = 143827318 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3639 j) = 143546095 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3640 j) = 143562275 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3641 j) = 143280968 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3642 j) = 143297139 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3643 j) = 143015747 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3644 j) = 143031932 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3645 j) = 142750465 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3646 j) = 142766653 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3647 j) = 142485087 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 3584 through 3647. -/
theorem lowerTwo_rows312_56 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3584+i) j) = 9390504770 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3584, lowerTwo_row_3585, lowerTwo_row_3586, lowerTwo_row_3587, lowerTwo_row_3588, lowerTwo_row_3589, lowerTwo_row_3590, lowerTwo_row_3591, lowerTwo_row_3592, lowerTwo_row_3593, lowerTwo_row_3594, lowerTwo_row_3595, lowerTwo_row_3596, lowerTwo_row_3597, lowerTwo_row_3598, lowerTwo_row_3599, lowerTwo_row_3600, lowerTwo_row_3601, lowerTwo_row_3602, lowerTwo_row_3603, lowerTwo_row_3604, lowerTwo_row_3605, lowerTwo_row_3606, lowerTwo_row_3607, lowerTwo_row_3608, lowerTwo_row_3609, lowerTwo_row_3610, lowerTwo_row_3611, lowerTwo_row_3612, lowerTwo_row_3613, lowerTwo_row_3614, lowerTwo_row_3615, lowerTwo_row_3616, lowerTwo_row_3617, lowerTwo_row_3618, lowerTwo_row_3619, lowerTwo_row_3620, lowerTwo_row_3621, lowerTwo_row_3622, lowerTwo_row_3623, lowerTwo_row_3624, lowerTwo_row_3625, lowerTwo_row_3626, lowerTwo_row_3627, lowerTwo_row_3628, lowerTwo_row_3629, lowerTwo_row_3630, lowerTwo_row_3631, lowerTwo_row_3632, lowerTwo_row_3633, lowerTwo_row_3634, lowerTwo_row_3635, lowerTwo_row_3636, lowerTwo_row_3637, lowerTwo_row_3638, lowerTwo_row_3639, lowerTwo_row_3640, lowerTwo_row_3641, lowerTwo_row_3642, lowerTwo_row_3643, lowerTwo_row_3644, lowerTwo_row_3645, lowerTwo_row_3646, lowerTwo_row_3647, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
