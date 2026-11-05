/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_39
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2560 j) = 358079763 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2561 j) = 357042717 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2562 j) = 357113668 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2563 j) = 356168680 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2564 j) = 356239308 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2565 j) = 356038833 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2566 j) = 354520902 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2567 j) = 354319129 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2568 j) = 354388904 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2569 j) = 353436231 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2570 j) = 353505608 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2571 j) = 352459551 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2572 j) = 351773865 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2573 j) = 351570793 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2574 j) = 351639295 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2575 j) = 350678781 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2576 j) = 350203952 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2577 j) = 350610097 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2578 j) = 350221735 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2579 j) = 350322595 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2580 j) = 351001128 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2581 j) = 349486968 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2582 j) = 349858564 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2583 j) = 350265702 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2584 j) = 349870221 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2585 j) = 349970590 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2586 j) = 349795363 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2587 j) = 349124346 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2588 j) = 349495441 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2589 j) = 349903583 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2590 j) = 349500896 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2591 j) = 348742318 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2592 j) = 349421978 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2593 j) = 348743603 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2594 j) = 349114174 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2595 j) = 349523260 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2596 j) = 348251260 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2597 j) = 348349484 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2598 j) = 349030189 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2599 j) = 348344300 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2600 j) = 348714295 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2601 j) = 348258775 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2602 j) = 347840237 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2603 j) = 347937812 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2604 j) = 348619495 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2605 j) = 347925953 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2606 j) = 347426124 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2607 j) = 347836118 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2608 j) = 347409902 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2609 j) = 347506771 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2610 j) = 348189433 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2611 j) = 346615174 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2612 j) = 346982967 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2613 j) = 347393850 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2614 j) = 346959764 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2615 j) = 347055946 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2616 j) = 346862936 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2617 j) = 346152590 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2618 j) = 346519711 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2619 j) = 346931416 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2620 j) = 346489357 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2621 j) = 345704443 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2622 j) = 346387924 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2623 j) = 345669478 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 2560 through 2623. -/
theorem lowerTwo_rows312_40 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2560+i) j) = 22391518246 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2560, lowerTwo_row_2561, lowerTwo_row_2562, lowerTwo_row_2563, lowerTwo_row_2564, lowerTwo_row_2565, lowerTwo_row_2566, lowerTwo_row_2567, lowerTwo_row_2568, lowerTwo_row_2569, lowerTwo_row_2570, lowerTwo_row_2571, lowerTwo_row_2572, lowerTwo_row_2573, lowerTwo_row_2574, lowerTwo_row_2575, lowerTwo_row_2576, lowerTwo_row_2577, lowerTwo_row_2578, lowerTwo_row_2579, lowerTwo_row_2580, lowerTwo_row_2581, lowerTwo_row_2582, lowerTwo_row_2583, lowerTwo_row_2584, lowerTwo_row_2585, lowerTwo_row_2586, lowerTwo_row_2587, lowerTwo_row_2588, lowerTwo_row_2589, lowerTwo_row_2590, lowerTwo_row_2591, lowerTwo_row_2592, lowerTwo_row_2593, lowerTwo_row_2594, lowerTwo_row_2595, lowerTwo_row_2596, lowerTwo_row_2597, lowerTwo_row_2598, lowerTwo_row_2599, lowerTwo_row_2600, lowerTwo_row_2601, lowerTwo_row_2602, lowerTwo_row_2603, lowerTwo_row_2604, lowerTwo_row_2605, lowerTwo_row_2606, lowerTwo_row_2607, lowerTwo_row_2608, lowerTwo_row_2609, lowerTwo_row_2610, lowerTwo_row_2611, lowerTwo_row_2612, lowerTwo_row_2613, lowerTwo_row_2614, lowerTwo_row_2615, lowerTwo_row_2616, lowerTwo_row_2617, lowerTwo_row_2618, lowerTwo_row_2619, lowerTwo_row_2620, lowerTwo_row_2621, lowerTwo_row_2622, lowerTwo_row_2623, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
