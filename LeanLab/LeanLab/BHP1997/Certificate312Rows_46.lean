/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2944 j) = 399919487 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2945 j) = 400029971 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2946 j) = 400839943 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2947 j) = 400993034 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2948 j) = 401381575 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2949 j) = 401918162 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2950 j) = 402349352 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2951 j) = 402462648 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2952 j) = 403279185 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2953 j) = 403435110 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2954 j) = 403826630 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2955 j) = 404369629 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2956 j) = 404803835 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2957 j) = 404919960 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2958 j) = 405743090 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2959 j) = 405901897 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2960 j) = 406296323 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2961 j) = 406845707 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2962 j) = 407282839 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2963 j) = 407401775 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2964 j) = 408231260 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2965 j) = 408392838 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2966 j) = 408790209 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2967 j) = 409345865 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2968 j) = 409785890 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2969 j) = 409907646 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2970 j) = 410743558 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2971 j) = 410907952 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2972 j) = 411308277 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2973 j) = 411870254 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2974 j) = 412313284 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2975 j) = 412437864 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2976 j) = 413280283 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2977 j) = 413447580 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2978 j) = 413850833 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2979 j) = 414419262 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2980 j) = 414865334 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2981 j) = 414992770 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2982 j) = 415841783 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2983 j) = 416011984 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2984 j) = 416418261 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2985 j) = 416993213 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2986 j) = 417442308 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2987 j) = 417572647 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2988 j) = 418428380 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2989 j) = 418601500 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2990 j) = 419010842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2991 j) = 419592387 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2992 j) = 420044578 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2993 j) = 420177840 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2994 j) = 421040359 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2995 j) = 421216477 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2996 j) = 421628902 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2997 j) = 422217129 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2998 j) = 422672446 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2999 j) = 422808717 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3000 j) = 423678079 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3001 j) = 423857197 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3002 j) = 424272786 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3003 j) = 424867812 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3004 j) = 425326267 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3005 j) = 425465591 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3006 j) = 426341903 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3007 j) = 426524069 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2944 through 3007. -/
theorem lowerTwo_rows312_46 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2944+i) j) = 26430944568 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2944, lowerTwo_row_2945, lowerTwo_row_2946, lowerTwo_row_2947, lowerTwo_row_2948, lowerTwo_row_2949, lowerTwo_row_2950, lowerTwo_row_2951, lowerTwo_row_2952, lowerTwo_row_2953, lowerTwo_row_2954, lowerTwo_row_2955, lowerTwo_row_2956, lowerTwo_row_2957, lowerTwo_row_2958, lowerTwo_row_2959, lowerTwo_row_2960, lowerTwo_row_2961, lowerTwo_row_2962, lowerTwo_row_2963, lowerTwo_row_2964, lowerTwo_row_2965, lowerTwo_row_2966, lowerTwo_row_2967, lowerTwo_row_2968, lowerTwo_row_2969, lowerTwo_row_2970, lowerTwo_row_2971, lowerTwo_row_2972, lowerTwo_row_2973, lowerTwo_row_2974, lowerTwo_row_2975, lowerTwo_row_2976, lowerTwo_row_2977, lowerTwo_row_2978, lowerTwo_row_2979, lowerTwo_row_2980, lowerTwo_row_2981, lowerTwo_row_2982, lowerTwo_row_2983, lowerTwo_row_2984, lowerTwo_row_2985, lowerTwo_row_2986, lowerTwo_row_2987, lowerTwo_row_2988, lowerTwo_row_2989, lowerTwo_row_2990, lowerTwo_row_2991, lowerTwo_row_2992, lowerTwo_row_2993, lowerTwo_row_2994, lowerTwo_row_2995, lowerTwo_row_2996, lowerTwo_row_2997, lowerTwo_row_2998, lowerTwo_row_2999, lowerTwo_row_3000, lowerTwo_row_3001, lowerTwo_row_3002, lowerTwo_row_3003, lowerTwo_row_3004, lowerTwo_row_3005, lowerTwo_row_3006, lowerTwo_row_3007, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
