/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_16

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1088 j) = 279675161 := by decide
private theorem lowerTwo_row_1089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1089 j) = 279828348 := by decide
private theorem lowerTwo_row_1090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1090 j) = 279981757 := by decide
private theorem lowerTwo_row_1091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1091 j) = 279310860 := by decide
private theorem lowerTwo_row_1092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1092 j) = 279464226 := by decide
private theorem lowerTwo_row_1093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1093 j) = 277969163 := by decide
private theorem lowerTwo_row_1094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1094 j) = 277298408 := by decide
private theorem lowerTwo_row_1095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1095 j) = 275805303 := by decide
private theorem lowerTwo_row_1096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1096 j) = 275134958 := by decide
private theorem lowerTwo_row_1097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1097 j) = 273643816 := by decide
private theorem lowerTwo_row_1098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1098 j) = 272973897 := by decide
private theorem lowerTwo_row_1099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1099 j) = 271484688 := by decide
private theorem lowerTwo_row_1100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1100 j) = 270815178 := by decide
private theorem lowerTwo_row_1101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1101 j) = 269327923 := by decide
private theorem lowerTwo_row_1102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1102 j) = 268658841 := by decide
private theorem lowerTwo_row_1103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1103 j) = 267173483 := by decide
private theorem lowerTwo_row_1104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1104 j) = 266504807 := by decide
private theorem lowerTwo_row_1105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1105 j) = 265021385 := by decide
private theorem lowerTwo_row_1106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1106 j) = 264353117 := by decide
private theorem lowerTwo_row_1107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1107 j) = 262871613 := by decide
private theorem lowerTwo_row_1108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1108 j) = 262203731 := by decide
private theorem lowerTwo_row_1109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1109 j) = 260724119 := by decide
private theorem lowerTwo_row_1110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1110 j) = 260056648 := by decide
private theorem lowerTwo_row_1111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1111 j) = 258578936 := by decide
private theorem lowerTwo_row_1112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1112 j) = 257911853 := by decide
private theorem lowerTwo_row_1113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1113 j) = 256436037 := by decide
private theorem lowerTwo_row_1114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1114 j) = 255769336 := by decide
private theorem lowerTwo_row_1115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1115 j) = 254770756 := by decide
private theorem lowerTwo_row_1116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1116 j) = 275007892 := by decide
private theorem lowerTwo_row_1117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1117 j) = 275634999 := by decide
private theorem lowerTwo_row_1118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1118 j) = 276261449 := by decide
private theorem lowerTwo_row_1119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1119 j) = 276058153 := by decide
private theorem lowerTwo_row_1120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1120 j) = 276682788 := by decide
private theorem lowerTwo_row_1121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1121 j) = 276477479 := by decide
private theorem lowerTwo_row_1122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1122 j) = 277100307 := by decide
private theorem lowerTwo_row_1123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1123 j) = 276892995 := by decide
private theorem lowerTwo_row_1124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1124 j) = 277514057 := by decide
private theorem lowerTwo_row_1125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1125 j) = 278134501 := by decide
private theorem lowerTwo_row_1126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1126 j) = 277924058 := by decide
private theorem lowerTwo_row_1127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1127 j) = 278542722 := by decide
private theorem lowerTwo_row_1128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1128 j) = 278330299 := by decide
private theorem lowerTwo_row_1129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1129 j) = 278947201 := by decide
private theorem lowerTwo_row_1130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1130 j) = 278732812 := by decide
private theorem lowerTwo_row_1131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1131 j) = 279347962 := by decide
private theorem lowerTwo_row_1132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1132 j) = 279962526 := by decide
private theorem lowerTwo_row_1133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1133 j) = 279745001 := by decide
private theorem lowerTwo_row_1134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1134 j) = 280357803 := by decide
private theorem lowerTwo_row_1135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1135 j) = 280138318 := by decide
private theorem lowerTwo_row_1136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1136 j) = 280749377 := by decide
private theorem lowerTwo_row_1137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1137 j) = 280527937 := by decide
private theorem lowerTwo_row_1138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1138 j) = 281137263 := by decide
private theorem lowerTwo_row_1139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1139 j) = 281746006 := by decide
private theorem lowerTwo_row_1140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1140 j) = 281521450 := by decide
private theorem lowerTwo_row_1141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1141 j) = 282128451 := by decide
private theorem lowerTwo_row_1142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1142 j) = 281901971 := by decide
private theorem lowerTwo_row_1143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1143 j) = 282507238 := by decide
private theorem lowerTwo_row_1144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1144 j) = 282278809 := by decide
private theorem lowerTwo_row_1145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1145 j) = 282882361 := by decide
private theorem lowerTwo_row_1146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1146 j) = 283485317 := by decide
private theorem lowerTwo_row_1147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1147 j) = 283253745 := by decide
private theorem lowerTwo_row_1148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1148 j) = 283854923 := by decide
private theorem lowerTwo_row_1149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1149 j) = 283621335 := by decide
private theorem lowerTwo_row_1150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1150 j) = 284220704 := by decide
private theorem lowerTwo_row_1151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1151 j) = 283985104 := by decide

/-- Page 51. Exact E2 row block 1088 through 1151. -/
theorem lowerTwo_rows312_17 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1088+i) j) = 17601343661 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1088, lowerTwo_row_1089, lowerTwo_row_1090, lowerTwo_row_1091, lowerTwo_row_1092, lowerTwo_row_1093, lowerTwo_row_1094, lowerTwo_row_1095, lowerTwo_row_1096, lowerTwo_row_1097, lowerTwo_row_1098, lowerTwo_row_1099, lowerTwo_row_1100, lowerTwo_row_1101, lowerTwo_row_1102, lowerTwo_row_1103, lowerTwo_row_1104, lowerTwo_row_1105, lowerTwo_row_1106, lowerTwo_row_1107, lowerTwo_row_1108, lowerTwo_row_1109, lowerTwo_row_1110, lowerTwo_row_1111, lowerTwo_row_1112, lowerTwo_row_1113, lowerTwo_row_1114, lowerTwo_row_1115, lowerTwo_row_1116, lowerTwo_row_1117, lowerTwo_row_1118, lowerTwo_row_1119, lowerTwo_row_1120, lowerTwo_row_1121, lowerTwo_row_1122, lowerTwo_row_1123, lowerTwo_row_1124, lowerTwo_row_1125, lowerTwo_row_1126, lowerTwo_row_1127, lowerTwo_row_1128, lowerTwo_row_1129, lowerTwo_row_1130, lowerTwo_row_1131, lowerTwo_row_1132, lowerTwo_row_1133, lowerTwo_row_1134, lowerTwo_row_1135, lowerTwo_row_1136, lowerTwo_row_1137, lowerTwo_row_1138, lowerTwo_row_1139, lowerTwo_row_1140, lowerTwo_row_1141, lowerTwo_row_1142, lowerTwo_row_1143, lowerTwo_row_1144, lowerTwo_row_1145, lowerTwo_row_1146, lowerTwo_row_1147, lowerTwo_row_1148, lowerTwo_row_1149, lowerTwo_row_1150, lowerTwo_row_1151, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
