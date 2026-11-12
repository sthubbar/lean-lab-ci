/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2880 j) = 375558959 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2881 j) = 375682617 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2882 j) = 376040622 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2883 j) = 376510352 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2884 j) = 376910775 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2885 j) = 376994619 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2886 j) = 377742876 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2887 j) = 377869129 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2888 j) = 378229835 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2889 j) = 378705578 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2890 j) = 379108688 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2891 j) = 379195179 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2892 j) = 379949527 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2893 j) = 380078410 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2894 j) = 380441888 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2895 j) = 380923626 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2896 j) = 381329549 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2897 j) = 381418676 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2898 j) = 382179252 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2899 j) = 382310760 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2900 j) = 382676999 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2901 j) = 383164770 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2902 j) = 383573363 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2903 j) = 383665121 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2904 j) = 384431609 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2905 j) = 384565742 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2906 j) = 384934617 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2907 j) = 385428205 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2908 j) = 385839539 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2909 j) = 385933867 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2910 j) = 386706320 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2911 j) = 386843062 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2912 j) = 387214648 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2913 j) = 387714145 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2914 j) = 388128229 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2915 j) = 388225136 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2916 j) = 389003692 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2917 j) = 389143068 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2918 j) = 389517379 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2919 j) = 390022871 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2920 j) = 390439743 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2921 j) = 390539255 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2922 j) = 391323946 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2923 j) = 391466014 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2924 j) = 391843091 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2925 j) = 392354659 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2926 j) = 392774312 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2927 j) = 392876521 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2928 j) = 393667442 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2929 j) = 393812189 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2930 j) = 394192087 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2931 j) = 394709780 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2932 j) = 395132266 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2933 j) = 395237196 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2934 j) = 396034366 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2935 j) = 396181863 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2936 j) = 396564640 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2937 j) = 397088541 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2938 j) = 397513872 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2939 j) = 397621596 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2940 j) = 398425136 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2941 j) = 398575408 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2942 j) = 398961050 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2943 j) = 399491218 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2880 through 2943. -/
theorem lowerTwo_rows312_45 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2880+i) j) = 24780739490 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2880, lowerTwo_row_2881, lowerTwo_row_2882, lowerTwo_row_2883, lowerTwo_row_2884, lowerTwo_row_2885, lowerTwo_row_2886, lowerTwo_row_2887, lowerTwo_row_2888, lowerTwo_row_2889, lowerTwo_row_2890, lowerTwo_row_2891, lowerTwo_row_2892, lowerTwo_row_2893, lowerTwo_row_2894, lowerTwo_row_2895, lowerTwo_row_2896, lowerTwo_row_2897, lowerTwo_row_2898, lowerTwo_row_2899, lowerTwo_row_2900, lowerTwo_row_2901, lowerTwo_row_2902, lowerTwo_row_2903, lowerTwo_row_2904, lowerTwo_row_2905, lowerTwo_row_2906, lowerTwo_row_2907, lowerTwo_row_2908, lowerTwo_row_2909, lowerTwo_row_2910, lowerTwo_row_2911, lowerTwo_row_2912, lowerTwo_row_2913, lowerTwo_row_2914, lowerTwo_row_2915, lowerTwo_row_2916, lowerTwo_row_2917, lowerTwo_row_2918, lowerTwo_row_2919, lowerTwo_row_2920, lowerTwo_row_2921, lowerTwo_row_2922, lowerTwo_row_2923, lowerTwo_row_2924, lowerTwo_row_2925, lowerTwo_row_2926, lowerTwo_row_2927, lowerTwo_row_2928, lowerTwo_row_2929, lowerTwo_row_2930, lowerTwo_row_2931, lowerTwo_row_2932, lowerTwo_row_2933, lowerTwo_row_2934, lowerTwo_row_2935, lowerTwo_row_2936, lowerTwo_row_2937, lowerTwo_row_2938, lowerTwo_row_2939, lowerTwo_row_2940, lowerTwo_row_2941, lowerTwo_row_2942, lowerTwo_row_2943, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
