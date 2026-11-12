/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2496 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2496 j) = 387176672 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2497 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2497 j) = 386309021 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2498 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2498 j) = 386391973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2499 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2499 j) = 386204329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2500 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2500 j) = 385604761 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2501 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2501 j) = 384618407 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2502 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2502 j) = 384700790 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2503 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2503 j) = 383826887 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2504 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2504 j) = 383909040 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2505 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2505 j) = 383720619 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2506 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2506 j) = 382313193 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2507 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2507 j) = 382123697 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2508 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2508 j) = 382205315 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2509 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2509 j) = 381325011 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2510 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2510 j) = 381406397 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2511 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2511 j) = 380412393 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2512 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2512 j) = 379799347 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2513 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2513 j) = 379608996 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2514 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2514 j) = 379689760 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2515 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2515 j) = 378802983 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2516 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2516 j) = 378075673 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2517 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2517 j) = 377884676 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2518 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2518 j) = 377265112 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2519 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2519 j) = 377073903 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2520 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2520 j) = 377153801 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2521 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2521 j) = 375449353 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2522 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2522 j) = 375528195 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2523 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2523 j) = 375336274 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2524 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2524 j) = 374710102 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2525 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2525 j) = 374517931 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2526 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2526 j) = 373782637 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2527 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2527 j) = 372881703 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2528 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2528 j) = 372959617 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2529 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2529 j) = 372766734 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2530 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2530 j) = 372133810 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2531 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2531 j) = 371123152 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2532 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2532 j) = 371200360 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2533 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2533 j) = 370292546 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2534 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2534 j) = 370369517 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2535 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2535 j) = 370175639 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2536 j) = 368715051 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2537 j) = 368519999 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2538 j) = 368596263 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2539 j) = 367681446 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2540 j) = 367757406 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2541 j) = 366738437 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2542 j) = 366090735 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2543 j) = 365894627 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2544 j) = 365969863 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2545 j) = 365047923 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2546 j) = 364295472 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2547 j) = 364098567 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2548 j) = 363443722 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2549 j) = 363246515 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2550 j) = 363320680 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2551 j) = 361560773 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2552 j) = 361633730 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2553 j) = 361435695 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2554 j) = 360773572 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2555 j) = 360575208 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2556 j) = 359814156 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2557 j) = 358876702 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2558 j) = 358948502 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2559 j) = 358749270 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2496 through 2559. -/
theorem lowerTwo_rows312_39 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2496+i) j) = 23872614640 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2496, lowerTwo_row_2497, lowerTwo_row_2498, lowerTwo_row_2499, lowerTwo_row_2500, lowerTwo_row_2501, lowerTwo_row_2502, lowerTwo_row_2503, lowerTwo_row_2504, lowerTwo_row_2505, lowerTwo_row_2506, lowerTwo_row_2507, lowerTwo_row_2508, lowerTwo_row_2509, lowerTwo_row_2510, lowerTwo_row_2511, lowerTwo_row_2512, lowerTwo_row_2513, lowerTwo_row_2514, lowerTwo_row_2515, lowerTwo_row_2516, lowerTwo_row_2517, lowerTwo_row_2518, lowerTwo_row_2519, lowerTwo_row_2520, lowerTwo_row_2521, lowerTwo_row_2522, lowerTwo_row_2523, lowerTwo_row_2524, lowerTwo_row_2525, lowerTwo_row_2526, lowerTwo_row_2527, lowerTwo_row_2528, lowerTwo_row_2529, lowerTwo_row_2530, lowerTwo_row_2531, lowerTwo_row_2532, lowerTwo_row_2533, lowerTwo_row_2534, lowerTwo_row_2535, lowerTwo_row_2536, lowerTwo_row_2537, lowerTwo_row_2538, lowerTwo_row_2539, lowerTwo_row_2540, lowerTwo_row_2541, lowerTwo_row_2542, lowerTwo_row_2543, lowerTwo_row_2544, lowerTwo_row_2545, lowerTwo_row_2546, lowerTwo_row_2547, lowerTwo_row_2548, lowerTwo_row_2549, lowerTwo_row_2550, lowerTwo_row_2551, lowerTwo_row_2552, lowerTwo_row_2553, lowerTwo_row_2554, lowerTwo_row_2555, lowerTwo_row_2556, lowerTwo_row_2557, lowerTwo_row_2558, lowerTwo_row_2559, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
