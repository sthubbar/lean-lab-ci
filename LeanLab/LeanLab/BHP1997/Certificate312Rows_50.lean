/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3200 j) = 447190023 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3201 j) = 446727550 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3202 j) = 445989782 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3203 j) = 444923255 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3204 j) = 444735345 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3205 j) = 443704316 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3206 j) = 442909743 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3207 j) = 442430877 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3208 j) = 441671733 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3209 j) = 440583483 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3210 j) = 440379008 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3211 j) = 439326016 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3212 j) = 438509525 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3213 j) = 438013544 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3214 j) = 437232227 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3215 j) = 436121484 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3216 j) = 435899663 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3217 j) = 434823916 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3218 j) = 433984649 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3219 j) = 433470808 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3220 j) = 432666434 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3221 j) = 431532362 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3222 j) = 431292431 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3223 j) = 430193050 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3224 j) = 429330132 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3225 j) = 428797652 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3226 j) = 427969384 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3227 j) = 426811030 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3228 j) = 426637014 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3229 j) = 425638337 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3230 j) = 424916182 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3231 j) = 424526920 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3232 j) = 423791520 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3233 j) = 422765678 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3234 j) = 422642220 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3235 j) = 421602840 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3236 j) = 420839842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3237 j) = 420414973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3238 j) = 419638966 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3239 j) = 418572651 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3240 j) = 418414686 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3241 j) = 417335506 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3242 j) = 416533222 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3243 j) = 416074552 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3244 j) = 415259181 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3245 j) = 414153091 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3246 j) = 413960819 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3247 j) = 412841391 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3248 j) = 411998678 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3249 j) = 411504780 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3250 j) = 410648546 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3251 j) = 409501112 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3252 j) = 409273019 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3253 j) = 408111711 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3254 j) = 407227055 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3255 j) = 406696552 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3256 j) = 405798453 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3257 j) = 404609273 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3258 j) = 404345583 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3259 j) = 403142973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3260 j) = 402217531 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3261 j) = 401651921 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3262 j) = 400712835 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3263 j) = 399482211 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 3200 through 3263. -/
theorem lowerTwo_rows312_50 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3200+i) j) = 27140701246 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3200, lowerTwo_row_3201, lowerTwo_row_3202, lowerTwo_row_3203, lowerTwo_row_3204, lowerTwo_row_3205, lowerTwo_row_3206, lowerTwo_row_3207, lowerTwo_row_3208, lowerTwo_row_3209, lowerTwo_row_3210, lowerTwo_row_3211, lowerTwo_row_3212, lowerTwo_row_3213, lowerTwo_row_3214, lowerTwo_row_3215, lowerTwo_row_3216, lowerTwo_row_3217, lowerTwo_row_3218, lowerTwo_row_3219, lowerTwo_row_3220, lowerTwo_row_3221, lowerTwo_row_3222, lowerTwo_row_3223, lowerTwo_row_3224, lowerTwo_row_3225, lowerTwo_row_3226, lowerTwo_row_3227, lowerTwo_row_3228, lowerTwo_row_3229, lowerTwo_row_3230, lowerTwo_row_3231, lowerTwo_row_3232, lowerTwo_row_3233, lowerTwo_row_3234, lowerTwo_row_3235, lowerTwo_row_3236, lowerTwo_row_3237, lowerTwo_row_3238, lowerTwo_row_3239, lowerTwo_row_3240, lowerTwo_row_3241, lowerTwo_row_3242, lowerTwo_row_3243, lowerTwo_row_3244, lowerTwo_row_3245, lowerTwo_row_3246, lowerTwo_row_3247, lowerTwo_row_3248, lowerTwo_row_3249, lowerTwo_row_3250, lowerTwo_row_3251, lowerTwo_row_3252, lowerTwo_row_3253, lowerTwo_row_3254, lowerTwo_row_3255, lowerTwo_row_3256, lowerTwo_row_3257, lowerTwo_row_3258, lowerTwo_row_3259, lowerTwo_row_3260, lowerTwo_row_3261, lowerTwo_row_3262, lowerTwo_row_3263, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
