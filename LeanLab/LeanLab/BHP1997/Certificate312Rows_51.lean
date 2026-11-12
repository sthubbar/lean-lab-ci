/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3264 j) = 399182802 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3265 j) = 397938216 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3266 j) = 396970645 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3267 j) = 396368329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3268 j) = 395386594 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3269 j) = 394112867 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3270 j) = 393776085 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3271 j) = 392487806 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3272 j) = 391476693 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3273 j) = 390836791 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3274 j) = 389811894 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3275 j) = 388495045 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3276 j) = 388121476 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3277 j) = 386790460 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3278 j) = 385736721 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3279 j) = 385059711 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3280 j) = 383991613 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3281 j) = 382630999 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3282 j) = 382219688 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3283 j) = 380844389 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3284 j) = 379746194 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3285 j) = 379030362 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3286 j) = 377917169 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3287 j) = 376511072 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3288 j) = 376060660 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3289 j) = 374640057 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3290 j) = 373496856 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3291 j) = 372742240 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3292 j) = 371584345 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3293 j) = 370133475 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3294 j) = 369644468 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3295 j) = 368178515 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3296 j) = 366989850 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3297 j) = 366195549 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3298 j) = 364991513 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3299 j) = 363493987 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3300 j) = 362964529 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3301 j) = 361451253 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3302 j) = 360215234 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3303 j) = 359379928 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3304 j) = 358128737 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3305 j) = 356583956 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3306 j) = 356013970 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3307 j) = 354453627 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3308 j) = 353170679 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3309 j) = 352294406 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3310 j) = 350995608 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3311 j) = 349402681 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3312 j) = 348790918 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3313 j) = 347181765 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3314 j) = 345849769 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3315 j) = 344930517 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3316 j) = 343582171 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3317 j) = 341939629 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3318 j) = 341285063 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3319 j) = 339626300 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3320 j) = 338244949 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3321 j) = 337282910 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3322 j) = 335885103 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3323 j) = 334192433 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3324 j) = 333494451 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3325 j) = 331784853 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3326 j) = 330352502 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3327 j) = 329345742 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 3264 through 3327. -/
theorem lowerTwo_rows312_51 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3264+i) j) = 23452418819 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3264, lowerTwo_row_3265, lowerTwo_row_3266, lowerTwo_row_3267, lowerTwo_row_3268, lowerTwo_row_3269, lowerTwo_row_3270, lowerTwo_row_3271, lowerTwo_row_3272, lowerTwo_row_3273, lowerTwo_row_3274, lowerTwo_row_3275, lowerTwo_row_3276, lowerTwo_row_3277, lowerTwo_row_3278, lowerTwo_row_3279, lowerTwo_row_3280, lowerTwo_row_3281, lowerTwo_row_3282, lowerTwo_row_3283, lowerTwo_row_3284, lowerTwo_row_3285, lowerTwo_row_3286, lowerTwo_row_3287, lowerTwo_row_3288, lowerTwo_row_3289, lowerTwo_row_3290, lowerTwo_row_3291, lowerTwo_row_3292, lowerTwo_row_3293, lowerTwo_row_3294, lowerTwo_row_3295, lowerTwo_row_3296, lowerTwo_row_3297, lowerTwo_row_3298, lowerTwo_row_3299, lowerTwo_row_3300, lowerTwo_row_3301, lowerTwo_row_3302, lowerTwo_row_3303, lowerTwo_row_3304, lowerTwo_row_3305, lowerTwo_row_3306, lowerTwo_row_3307, lowerTwo_row_3308, lowerTwo_row_3309, lowerTwo_row_3310, lowerTwo_row_3311, lowerTwo_row_3312, lowerTwo_row_3313, lowerTwo_row_3314, lowerTwo_row_3315, lowerTwo_row_3316, lowerTwo_row_3317, lowerTwo_row_3318, lowerTwo_row_3319, lowerTwo_row_3320, lowerTwo_row_3321, lowerTwo_row_3322, lowerTwo_row_3323, lowerTwo_row_3324, lowerTwo_row_3325, lowerTwo_row_3326, lowerTwo_row_3327, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
