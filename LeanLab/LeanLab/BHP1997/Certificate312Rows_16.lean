/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1024 j) = 292837602 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1025 j) = 292175091 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1026 j) = 292326954 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1027 j) = 292479028 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1028 j) = 291816109 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1029 j) = 291968197 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1030 j) = 291305091 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1031 j) = 291457128 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1032 j) = 290793857 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1033 j) = 290945907 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1034 j) = 291098177 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1035 j) = 290434461 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1036 j) = 290586722 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1037 j) = 289922817 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1038 j) = 290075064 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1039 j) = 289410973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1040 j) = 289563183 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1041 j) = 289715655 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1042 j) = 289051118 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1043 j) = 289203545 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1044 j) = 288538821 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1045 j) = 288691238 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1046 j) = 288026329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1047 j) = 288178713 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1048 j) = 288331329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1049 j) = 287665976 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1050 j) = 287818573 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1051 j) = 287153021 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1052 j) = 287305583 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1053 j) = 286639818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1054 j) = 286792354 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1055 j) = 286945147 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1056 j) = 286278917 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1057 j) = 286431659 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1058 j) = 285765234 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1059 j) = 285917943 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1060 j) = 285251313 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1061 j) = 285404000 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1062 j) = 285556933 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1063 j) = 284889812 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1064 j) = 285042710 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1065 j) = 284375386 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1066 j) = 284528252 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1067 j) = 283860705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1068 j) = 284013532 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1069 j) = 284166608 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1070 j) = 283498577 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1071 j) = 283651591 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1072 j) = 282983366 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1073 j) = 283136354 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1074 j) = 282467893 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1075 j) = 282620843 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1076 j) = 282774047 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1077 j) = 282105076 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1078 j) = 282258234 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1079 j) = 281589044 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1080 j) = 281742168 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1081 j) = 281072747 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1082 j) = 281225808 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1083 j) = 281379125 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1084 j) = 280709212 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1085 j) = 280862480 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1086 j) = 280192323 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1087 j) = 280345550 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1024 through 1087. -/
theorem lowerTwo_rows312_16 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1024+i) j) = 18335351023 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1024, lowerTwo_row_1025, lowerTwo_row_1026, lowerTwo_row_1027, lowerTwo_row_1028, lowerTwo_row_1029, lowerTwo_row_1030, lowerTwo_row_1031, lowerTwo_row_1032, lowerTwo_row_1033, lowerTwo_row_1034, lowerTwo_row_1035, lowerTwo_row_1036, lowerTwo_row_1037, lowerTwo_row_1038, lowerTwo_row_1039, lowerTwo_row_1040, lowerTwo_row_1041, lowerTwo_row_1042, lowerTwo_row_1043, lowerTwo_row_1044, lowerTwo_row_1045, lowerTwo_row_1046, lowerTwo_row_1047, lowerTwo_row_1048, lowerTwo_row_1049, lowerTwo_row_1050, lowerTwo_row_1051, lowerTwo_row_1052, lowerTwo_row_1053, lowerTwo_row_1054, lowerTwo_row_1055, lowerTwo_row_1056, lowerTwo_row_1057, lowerTwo_row_1058, lowerTwo_row_1059, lowerTwo_row_1060, lowerTwo_row_1061, lowerTwo_row_1062, lowerTwo_row_1063, lowerTwo_row_1064, lowerTwo_row_1065, lowerTwo_row_1066, lowerTwo_row_1067, lowerTwo_row_1068, lowerTwo_row_1069, lowerTwo_row_1070, lowerTwo_row_1071, lowerTwo_row_1072, lowerTwo_row_1073, lowerTwo_row_1074, lowerTwo_row_1075, lowerTwo_row_1076, lowerTwo_row_1077, lowerTwo_row_1078, lowerTwo_row_1079, lowerTwo_row_1080, lowerTwo_row_1081, lowerTwo_row_1082, lowerTwo_row_1083, lowerTwo_row_1084, lowerTwo_row_1085, lowerTwo_row_1086, lowerTwo_row_1087, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
