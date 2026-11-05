/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_47
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3072 j) = 457405593 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3073 j) = 457622738 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3074 j) = 458077770 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3075 j) = 458757311 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3076 j) = 459255560 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3077 j) = 459432839 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3078 j) = 460395530 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3079 j) = 460616020 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3080 j) = 461074502 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3081 j) = 461761416 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3082 j) = 462263166 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3083 j) = 462443812 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3084 j) = 463414000 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3085 j) = 463637912 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3086 j) = 464099861 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3087 j) = 464794240 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3088 j) = 465299547 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3089 j) = 465483534 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3090 j) = 466461448 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3091 j) = 466688758 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3092 j) = 467154248 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3093 j) = 467856206 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3094 j) = 468365108 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3095 j) = 468552500 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3096 j) = 469538203 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3097 j) = 469768979 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3098 j) = 470238067 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3099 j) = 470947718 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3100 j) = 471460258 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3101 j) = 471651137 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3102 j) = 472644682 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3103 j) = 472878973 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3104 j) = 473351751 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3105 j) = 474069142 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3106 j) = 474585366 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3107 j) = 474779797 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3108 j) = 475781360 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3109 j) = 476019192 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3110 j) = 476495678 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3111 j) = 477220986 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3112 j) = 477740916 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3113 j) = 477938933 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3114 j) = 478948562 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3115 j) = 479190040 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3116 j) = 479670251 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3117 j) = 480403537 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3118 j) = 480927311 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3119 j) = 481128975 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3120 j) = 482146760 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3121 j) = 482391953 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3122 j) = 482875959 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3123 j) = 483617361 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3124 j) = 484144991 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3125 j) = 484350289 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3126 j) = 485376308 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3127 j) = 485625111 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3128 j) = 486112888 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3129 j) = 486862164 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3130 j) = 487393479 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3131 j) = 487602341 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3132 j) = 488636321 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3133 j) = 488888682 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3134 j) = 489380177 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3135 j) = 489544430 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 3072 through 3135. -/
theorem lowerTwo_rows312_48 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3072+i) j) = 30293242647 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3072, lowerTwo_row_3073, lowerTwo_row_3074, lowerTwo_row_3075, lowerTwo_row_3076, lowerTwo_row_3077, lowerTwo_row_3078, lowerTwo_row_3079, lowerTwo_row_3080, lowerTwo_row_3081, lowerTwo_row_3082, lowerTwo_row_3083, lowerTwo_row_3084, lowerTwo_row_3085, lowerTwo_row_3086, lowerTwo_row_3087, lowerTwo_row_3088, lowerTwo_row_3089, lowerTwo_row_3090, lowerTwo_row_3091, lowerTwo_row_3092, lowerTwo_row_3093, lowerTwo_row_3094, lowerTwo_row_3095, lowerTwo_row_3096, lowerTwo_row_3097, lowerTwo_row_3098, lowerTwo_row_3099, lowerTwo_row_3100, lowerTwo_row_3101, lowerTwo_row_3102, lowerTwo_row_3103, lowerTwo_row_3104, lowerTwo_row_3105, lowerTwo_row_3106, lowerTwo_row_3107, lowerTwo_row_3108, lowerTwo_row_3109, lowerTwo_row_3110, lowerTwo_row_3111, lowerTwo_row_3112, lowerTwo_row_3113, lowerTwo_row_3114, lowerTwo_row_3115, lowerTwo_row_3116, lowerTwo_row_3117, lowerTwo_row_3118, lowerTwo_row_3119, lowerTwo_row_3120, lowerTwo_row_3121, lowerTwo_row_3122, lowerTwo_row_3123, lowerTwo_row_3124, lowerTwo_row_3125, lowerTwo_row_3126, lowerTwo_row_3127, lowerTwo_row_3128, lowerTwo_row_3129, lowerTwo_row_3130, lowerTwo_row_3131, lowerTwo_row_3132, lowerTwo_row_3133, lowerTwo_row_3134, lowerTwo_row_3135, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
