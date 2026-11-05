/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_54
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3520 j) = 159340789 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3521 j) = 159063837 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3522 j) = 159079681 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3523 j) = 158802647 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3524 j) = 158818517 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3525 j) = 158541423 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3526 j) = 158557277 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3527 j) = 158280138 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3528 j) = 158296015 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3529 j) = 158018786 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3530 j) = 158034672 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3531 j) = 157757387 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3532 j) = 157773280 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3533 j) = 157495934 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3534 j) = 157511836 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3535 j) = 157234410 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3536 j) = 157250326 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3537 j) = 156972832 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3538 j) = 156988758 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3539 j) = 156711197 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3540 j) = 156727134 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3541 j) = 156449498 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3542 j) = 156465440 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3543 j) = 156187745 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3544 j) = 156203688 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3545 j) = 155925925 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3546 j) = 155941886 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3547 j) = 155664063 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3548 j) = 155680020 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3549 j) = 155402118 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3550 j) = 155418082 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3551 j) = 155140127 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3552 j) = 155156107 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3553 j) = 154878063 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3554 j) = 154894048 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3555 j) = 154615940 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3556 j) = 154631925 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3557 j) = 154353775 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3558 j) = 154369744 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3559 j) = 154091512 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3560 j) = 154107516 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3561 j) = 153829208 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3562 j) = 153845226 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3563 j) = 153566840 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3564 j) = 153582840 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3565 j) = 153304398 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3566 j) = 153320414 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3567 j) = 153041887 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3568 j) = 153057918 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3569 j) = 152779324 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3570 j) = 152795366 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3571 j) = 152516706 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3572 j) = 152532741 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3573 j) = 152254001 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3574 j) = 152270062 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3575 j) = 151991245 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3576 j) = 152007296 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3577 j) = 151728426 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3578 j) = 151744486 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3579 j) = 151465528 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3580 j) = 151481589 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3581 j) = 151202577 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3582 j) = 151218640 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3583 j) = 150939545 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 3520 through 3583. -/
theorem lowerTwo_rows312_55 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3520+i) j) = 9929310361 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3520, lowerTwo_row_3521, lowerTwo_row_3522, lowerTwo_row_3523, lowerTwo_row_3524, lowerTwo_row_3525, lowerTwo_row_3526, lowerTwo_row_3527, lowerTwo_row_3528, lowerTwo_row_3529, lowerTwo_row_3530, lowerTwo_row_3531, lowerTwo_row_3532, lowerTwo_row_3533, lowerTwo_row_3534, lowerTwo_row_3535, lowerTwo_row_3536, lowerTwo_row_3537, lowerTwo_row_3538, lowerTwo_row_3539, lowerTwo_row_3540, lowerTwo_row_3541, lowerTwo_row_3542, lowerTwo_row_3543, lowerTwo_row_3544, lowerTwo_row_3545, lowerTwo_row_3546, lowerTwo_row_3547, lowerTwo_row_3548, lowerTwo_row_3549, lowerTwo_row_3550, lowerTwo_row_3551, lowerTwo_row_3552, lowerTwo_row_3553, lowerTwo_row_3554, lowerTwo_row_3555, lowerTwo_row_3556, lowerTwo_row_3557, lowerTwo_row_3558, lowerTwo_row_3559, lowerTwo_row_3560, lowerTwo_row_3561, lowerTwo_row_3562, lowerTwo_row_3563, lowerTwo_row_3564, lowerTwo_row_3565, lowerTwo_row_3566, lowerTwo_row_3567, lowerTwo_row_3568, lowerTwo_row_3569, lowerTwo_row_3570, lowerTwo_row_3571, lowerTwo_row_3572, lowerTwo_row_3573, lowerTwo_row_3574, lowerTwo_row_3575, lowerTwo_row_3576, lowerTwo_row_3577, lowerTwo_row_3578, lowerTwo_row_3579, lowerTwo_row_3580, lowerTwo_row_3581, lowerTwo_row_3582, lowerTwo_row_3583, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
