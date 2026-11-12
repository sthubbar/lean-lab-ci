/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3456 j) = 167668633 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3457 j) = 167393626 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3458 j) = 167409139 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3459 j) = 167134072 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3460 j) = 167149586 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3461 j) = 166874490 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3462 j) = 166890019 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3463 j) = 166614829 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3464 j) = 166630380 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3465 j) = 166355159 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3466 j) = 166370725 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3467 j) = 166095420 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3468 j) = 166110995 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3469 j) = 165835633 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3470 j) = 165851211 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3471 j) = 165575818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3472 j) = 165591411 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3473 j) = 165315947 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3474 j) = 165331540 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3475 j) = 165056008 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3476 j) = 165071622 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3477 j) = 164796050 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3478 j) = 164811678 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3479 j) = 164536025 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3480 j) = 164551663 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3481 j) = 164275953 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3482 j) = 164291601 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3483 j) = 164015834 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3484 j) = 164031504 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3485 j) = 163755679 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3486 j) = 163771347 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3487 j) = 163495445 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3488 j) = 163511140 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3489 j) = 163235190 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3490 j) = 163250895 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3491 j) = 162974875 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3492 j) = 162990595 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3493 j) = 162714504 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3494 j) = 162730233 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3495 j) = 162454095 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3496 j) = 162469815 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3497 j) = 162193632 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3498 j) = 162209361 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3499 j) = 161933107 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3500 j) = 161948850 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3501 j) = 161672531 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3502 j) = 161688270 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3503 j) = 161411896 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3504 j) = 161427661 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3505 j) = 161151209 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3506 j) = 161166998 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3507 j) = 160890484 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3508 j) = 160906265 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3509 j) = 160629693 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3510 j) = 160645484 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3511 j) = 160368842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3512 j) = 160384661 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3513 j) = 160107955 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3514 j) = 160123777 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3515 j) = 159847010 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3516 j) = 159862836 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3517 j) = 159586002 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3518 j) = 159601840 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3519 j) = 159324935 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 3456 through 3519. -/
theorem lowerTwo_rows312_54 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3456+i) j) = 10464073683 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3456, lowerTwo_row_3457, lowerTwo_row_3458, lowerTwo_row_3459, lowerTwo_row_3460, lowerTwo_row_3461, lowerTwo_row_3462, lowerTwo_row_3463, lowerTwo_row_3464, lowerTwo_row_3465, lowerTwo_row_3466, lowerTwo_row_3467, lowerTwo_row_3468, lowerTwo_row_3469, lowerTwo_row_3470, lowerTwo_row_3471, lowerTwo_row_3472, lowerTwo_row_3473, lowerTwo_row_3474, lowerTwo_row_3475, lowerTwo_row_3476, lowerTwo_row_3477, lowerTwo_row_3478, lowerTwo_row_3479, lowerTwo_row_3480, lowerTwo_row_3481, lowerTwo_row_3482, lowerTwo_row_3483, lowerTwo_row_3484, lowerTwo_row_3485, lowerTwo_row_3486, lowerTwo_row_3487, lowerTwo_row_3488, lowerTwo_row_3489, lowerTwo_row_3490, lowerTwo_row_3491, lowerTwo_row_3492, lowerTwo_row_3493, lowerTwo_row_3494, lowerTwo_row_3495, lowerTwo_row_3496, lowerTwo_row_3497, lowerTwo_row_3498, lowerTwo_row_3499, lowerTwo_row_3500, lowerTwo_row_3501, lowerTwo_row_3502, lowerTwo_row_3503, lowerTwo_row_3504, lowerTwo_row_3505, lowerTwo_row_3506, lowerTwo_row_3507, lowerTwo_row_3508, lowerTwo_row_3509, lowerTwo_row_3510, lowerTwo_row_3511, lowerTwo_row_3512, lowerTwo_row_3513, lowerTwo_row_3514, lowerTwo_row_3515, lowerTwo_row_3516, lowerTwo_row_3517, lowerTwo_row_3518, lowerTwo_row_3519, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
