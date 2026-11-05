/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_46
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3008 j) = 426942832 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3009 j) = 427544681 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3010 j) = 428006387 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3011 j) = 428148771 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3012 j) = 429032086 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3013 j) = 429217384 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3014 j) = 429639345 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3015 j) = 430248006 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3016 j) = 430712901 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3017 j) = 430858334 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3018 j) = 431748472 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3019 j) = 431936785 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3020 j) = 432361871 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3021 j) = 432977309 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3022 j) = 433445364 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3023 j) = 433593757 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3024 j) = 434490842 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3025 j) = 434682196 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3026 j) = 435110441 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3027 j) = 435732709 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3028 j) = 436203944 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3029 j) = 436355386 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3030 j) = 437259547 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3031 j) = 437453967 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3032 j) = 437885427 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3033 j) = 438514598 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3034 j) = 438989072 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3035 j) = 439143643 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3036 j) = 440054848 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3037 j) = 440252405 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3038 j) = 440687159 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3039 j) = 441323303 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3040 j) = 441801069 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3041 j) = 441958810 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3042 j) = 442877161 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3043 j) = 443077938 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3044 j) = 443515933 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3045 j) = 444159171 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3046 j) = 444640334 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3047 j) = 444801259 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3048 j) = 445726843 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3049 j) = 445930840 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3050 j) = 446372247 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3051 j) = 447022647 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3052 j) = 447507176 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3053 j) = 447671320 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3054 j) = 448604301 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3055 j) = 448811585 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3056 j) = 449256336 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3057 j) = 449914048 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3058 j) = 450401988 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3059 j) = 450569430 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3060 j) = 451509879 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3061 j) = 451720473 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3062 j) = 452168636 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3063 j) = 452833733 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3064 j) = 453325141 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3065 j) = 453495876 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3066 j) = 454443782 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3067 j) = 454657663 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3068 j) = 455109246 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3069 j) = 455781561 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3070 j) = 456276363 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3071 j) = 456450348 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 3008 through 3071. -/
theorem lowerTwo_rows312_47 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3008+i) j) = 28262946909 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3008, lowerTwo_row_3009, lowerTwo_row_3010, lowerTwo_row_3011, lowerTwo_row_3012, lowerTwo_row_3013, lowerTwo_row_3014, lowerTwo_row_3015, lowerTwo_row_3016, lowerTwo_row_3017, lowerTwo_row_3018, lowerTwo_row_3019, lowerTwo_row_3020, lowerTwo_row_3021, lowerTwo_row_3022, lowerTwo_row_3023, lowerTwo_row_3024, lowerTwo_row_3025, lowerTwo_row_3026, lowerTwo_row_3027, lowerTwo_row_3028, lowerTwo_row_3029, lowerTwo_row_3030, lowerTwo_row_3031, lowerTwo_row_3032, lowerTwo_row_3033, lowerTwo_row_3034, lowerTwo_row_3035, lowerTwo_row_3036, lowerTwo_row_3037, lowerTwo_row_3038, lowerTwo_row_3039, lowerTwo_row_3040, lowerTwo_row_3041, lowerTwo_row_3042, lowerTwo_row_3043, lowerTwo_row_3044, lowerTwo_row_3045, lowerTwo_row_3046, lowerTwo_row_3047, lowerTwo_row_3048, lowerTwo_row_3049, lowerTwo_row_3050, lowerTwo_row_3051, lowerTwo_row_3052, lowerTwo_row_3053, lowerTwo_row_3054, lowerTwo_row_3055, lowerTwo_row_3056, lowerTwo_row_3057, lowerTwo_row_3058, lowerTwo_row_3059, lowerTwo_row_3060, lowerTwo_row_3061, lowerTwo_row_3062, lowerTwo_row_3063, lowerTwo_row_3064, lowerTwo_row_3065, lowerTwo_row_3066, lowerTwo_row_3067, lowerTwo_row_3068, lowerTwo_row_3069, lowerTwo_row_3070, lowerTwo_row_3071, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
