/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2304 j) = 462995795 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2305 j) = 462283455 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2306 j) = 461685955 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2307 j) = 461511912 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2308 j) = 461067589 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2309 j) = 460893652 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2310 j) = 460990046 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2311 j) = 459578028 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2312 j) = 459673865 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2313 j) = 459499886 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2314 j) = 459052071 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2315 j) = 458878217 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2316 j) = 458276070 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2317 j) = 457556115 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2318 j) = 457652033 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2319 j) = 457478140 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2320 j) = 457026763 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2321 j) = 456152001 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2322 j) = 456247905 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2323 j) = 455524284 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2324 j) = 455620287 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2325 j) = 455446446 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2326 j) = 454288062 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2327 j) = 454113649 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2328 j) = 454209638 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2329 j) = 453482292 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2330 j) = 453578306 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2331 j) = 452698824 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2332 j) = 452239387 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2333 j) = 452065001 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2334 j) = 452161010 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2335 j) = 451429913 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2336 j) = 450817849 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2337 j) = 450643427 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2338 j) = 450180191 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2339 j) = 450005843 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2340 j) = 450101832 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2341 j) = 448656355 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2342 j) = 448751781 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2343 j) = 448577309 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2344 j) = 448110243 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2345 j) = 447935876 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2346 j) = 447318848 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2347 j) = 446579373 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2348 j) = 446674766 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2349 j) = 446500264 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2350 j) = 446029289 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2351 j) = 445139389 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2352 j) = 445234670 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2353 j) = 444491235 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2354 j) = 444586597 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2355 j) = 444412038 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2356 j) = 443219119 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2357 j) = 443043960 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2358 j) = 443139210 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2359 j) = 442391688 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2360 j) = 442486962 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2361 j) = 441591926 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2362 j) = 441112221 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2363 j) = 440936922 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2364 j) = 441032131 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2365 j) = 440280506 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2366 j) = 439652748 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2367 j) = 439477387 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2304 through 2367. -/
theorem lowerTwo_rows312_36 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2304+i) j) = 28874468552 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2304, lowerTwo_row_2305, lowerTwo_row_2306, lowerTwo_row_2307, lowerTwo_row_2308, lowerTwo_row_2309, lowerTwo_row_2310, lowerTwo_row_2311, lowerTwo_row_2312, lowerTwo_row_2313, lowerTwo_row_2314, lowerTwo_row_2315, lowerTwo_row_2316, lowerTwo_row_2317, lowerTwo_row_2318, lowerTwo_row_2319, lowerTwo_row_2320, lowerTwo_row_2321, lowerTwo_row_2322, lowerTwo_row_2323, lowerTwo_row_2324, lowerTwo_row_2325, lowerTwo_row_2326, lowerTwo_row_2327, lowerTwo_row_2328, lowerTwo_row_2329, lowerTwo_row_2330, lowerTwo_row_2331, lowerTwo_row_2332, lowerTwo_row_2333, lowerTwo_row_2334, lowerTwo_row_2335, lowerTwo_row_2336, lowerTwo_row_2337, lowerTwo_row_2338, lowerTwo_row_2339, lowerTwo_row_2340, lowerTwo_row_2341, lowerTwo_row_2342, lowerTwo_row_2343, lowerTwo_row_2344, lowerTwo_row_2345, lowerTwo_row_2346, lowerTwo_row_2347, lowerTwo_row_2348, lowerTwo_row_2349, lowerTwo_row_2350, lowerTwo_row_2351, lowerTwo_row_2352, lowerTwo_row_2353, lowerTwo_row_2354, lowerTwo_row_2355, lowerTwo_row_2356, lowerTwo_row_2357, lowerTwo_row_2358, lowerTwo_row_2359, lowerTwo_row_2360, lowerTwo_row_2361, lowerTwo_row_2362, lowerTwo_row_2363, lowerTwo_row_2364, lowerTwo_row_2365, lowerTwo_row_2366, lowerTwo_row_2367, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
