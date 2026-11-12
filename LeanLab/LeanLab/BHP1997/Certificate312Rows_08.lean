/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 512 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 513 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 514 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 515 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 516 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 517 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 518 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 519 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 520 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 521 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 522 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 523 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 524 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 525 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 526 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 527 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 528 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 529 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 530 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 531 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 532 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 533 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 534 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 535 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 536 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 537 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 538 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 539 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 540 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 541 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 542 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 543 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 544 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 545 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 546 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 547 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 548 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 549 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 550 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 551 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 552 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 553 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 554 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 555 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 556 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 557 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 558 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 559 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 560 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 561 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 562 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 563 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 564 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 565 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 566 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 567 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 568 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 569 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 570 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 571 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 572 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 573 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 574 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
private theorem lowerTwo_row_575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 575 j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply lowerTwo_grid_zero_of_cover
  change _ ∨ _ ∨ decide _ = true ∨ decide _ = true
  rw [decide_eq_true_eq, decide_eq_true_eq]
  unfold lowerTwoGridPoint
  omega
/-- Page 51. Exact E2 row block 512 through 575. -/
theorem lowerTwo_rows312_08 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (512+i) j) = 0 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_512, lowerTwo_row_513, lowerTwo_row_514, lowerTwo_row_515, lowerTwo_row_516, lowerTwo_row_517, lowerTwo_row_518, lowerTwo_row_519, lowerTwo_row_520, lowerTwo_row_521, lowerTwo_row_522, lowerTwo_row_523, lowerTwo_row_524, lowerTwo_row_525, lowerTwo_row_526, lowerTwo_row_527, lowerTwo_row_528, lowerTwo_row_529, lowerTwo_row_530, lowerTwo_row_531, lowerTwo_row_532, lowerTwo_row_533, lowerTwo_row_534, lowerTwo_row_535, lowerTwo_row_536, lowerTwo_row_537, lowerTwo_row_538, lowerTwo_row_539, lowerTwo_row_540, lowerTwo_row_541, lowerTwo_row_542, lowerTwo_row_543, lowerTwo_row_544, lowerTwo_row_545, lowerTwo_row_546, lowerTwo_row_547, lowerTwo_row_548, lowerTwo_row_549, lowerTwo_row_550, lowerTwo_row_551, lowerTwo_row_552, lowerTwo_row_553, lowerTwo_row_554, lowerTwo_row_555, lowerTwo_row_556, lowerTwo_row_557, lowerTwo_row_558, lowerTwo_row_559, lowerTwo_row_560, lowerTwo_row_561, lowerTwo_row_562, lowerTwo_row_563, lowerTwo_row_564, lowerTwo_row_565, lowerTwo_row_566, lowerTwo_row_567, lowerTwo_row_568, lowerTwo_row_569, lowerTwo_row_570, lowerTwo_row_571, lowerTwo_row_572, lowerTwo_row_573, lowerTwo_row_574, lowerTwo_row_575, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
