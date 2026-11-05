/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_37
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2432 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2432 j) = 414025330 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2433 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2433 j) = 413845708 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2434 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2434 j) = 413309640 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2435 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2435 j) = 413129907 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2436 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2436 j) = 412460705 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2437 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2437 j) = 411651249 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2438 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2438 j) = 411741407 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2439 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2439 j) = 411561360 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2440 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2440 j) = 411020150 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2441 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2441 j) = 410077015 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2442 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2442 j) = 410166819 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2443 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2443 j) = 409352143 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2444 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2444 j) = 409441914 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2445 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2445 j) = 409261422 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2446 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2446 j) = 407949082 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2447 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2447 j) = 407767758 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2448 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2448 j) = 407857157 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2449 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2449 j) = 407037177 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2450 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2450 j) = 407126435 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2451 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2451 j) = 406176765 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2452 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2452 j) = 405624254 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2453 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2453 j) = 405442405 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2454 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2454 j) = 405531295 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2455 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2455 j) = 404705938 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2456 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2456 j) = 404023174 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2457 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2457 j) = 403840907 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2458 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2458 j) = 403282980 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2459 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2459 j) = 403100583 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2460 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2460 j) = 403188969 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2461 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2461 j) = 401583656 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2462 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2462 j) = 401671184 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2463 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2463 j) = 401488369 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2464 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2464 j) = 400924907 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2465 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2465 j) = 400741956 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2466 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2466 j) = 400052431 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2467 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2467 j) = 399215203 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2468 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2468 j) = 399302160 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2469 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2469 j) = 399118779 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2470 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2470 j) = 398549693 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2471 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2471 j) = 397585812 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2472 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2472 j) = 397672337 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2473 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2473 j) = 396829389 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2474 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2474 j) = 396915792 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2475 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2475 j) = 396731791 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2476 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2476 j) = 395373674 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2477 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2477 j) = 395188705 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2478 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2478 j) = 395274641 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2479 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2479 j) = 394425855 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2480 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2480 j) = 394511675 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2481 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2481 j) = 393540716 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2482 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2482 j) = 392959277 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2483 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2483 j) = 392773679 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2484 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2484 j) = 392858968 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2485 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2485 j) = 392004263 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2486 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2486 j) = 391300123 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2487 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2487 j) = 391113951 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2488 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2488 j) = 390526604 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2489 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2489 j) = 390340306 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2490 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2490 j) = 390424890 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2491 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2491 j) = 388771856 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2492 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2492 j) = 388855508 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2493 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2493 j) = 388668602 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2494 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2494 j) = 388075235 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2495 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2495 j) = 387888142 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 2432 through 2495. -/
theorem lowerTwo_rows312_38 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2432+i) j) = 25666959777 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2432, lowerTwo_row_2433, lowerTwo_row_2434, lowerTwo_row_2435, lowerTwo_row_2436, lowerTwo_row_2437, lowerTwo_row_2438, lowerTwo_row_2439, lowerTwo_row_2440, lowerTwo_row_2441, lowerTwo_row_2442, lowerTwo_row_2443, lowerTwo_row_2444, lowerTwo_row_2445, lowerTwo_row_2446, lowerTwo_row_2447, lowerTwo_row_2448, lowerTwo_row_2449, lowerTwo_row_2450, lowerTwo_row_2451, lowerTwo_row_2452, lowerTwo_row_2453, lowerTwo_row_2454, lowerTwo_row_2455, lowerTwo_row_2456, lowerTwo_row_2457, lowerTwo_row_2458, lowerTwo_row_2459, lowerTwo_row_2460, lowerTwo_row_2461, lowerTwo_row_2462, lowerTwo_row_2463, lowerTwo_row_2464, lowerTwo_row_2465, lowerTwo_row_2466, lowerTwo_row_2467, lowerTwo_row_2468, lowerTwo_row_2469, lowerTwo_row_2470, lowerTwo_row_2471, lowerTwo_row_2472, lowerTwo_row_2473, lowerTwo_row_2474, lowerTwo_row_2475, lowerTwo_row_2476, lowerTwo_row_2477, lowerTwo_row_2478, lowerTwo_row_2479, lowerTwo_row_2480, lowerTwo_row_2481, lowerTwo_row_2482, lowerTwo_row_2483, lowerTwo_row_2484, lowerTwo_row_2485, lowerTwo_row_2486, lowerTwo_row_2487, lowerTwo_row_2488, lowerTwo_row_2489, lowerTwo_row_2490, lowerTwo_row_2491, lowerTwo_row_2492, lowerTwo_row_2493, lowerTwo_row_2494, lowerTwo_row_2495, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
