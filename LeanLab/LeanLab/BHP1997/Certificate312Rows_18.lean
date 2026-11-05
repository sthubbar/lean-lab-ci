/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_17

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1152 j) = 284582688 := by decide
private theorem lowerTwo_row_1153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1153 j) = 285179644 := by decide
private theorem lowerTwo_row_1154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1154 j) = 284940848 := by decide
private theorem lowerTwo_row_1155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1155 j) = 285536053 := by decide
private theorem lowerTwo_row_1156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1156 j) = 285295259 := by decide
private theorem lowerTwo_row_1157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1157 j) = 285888670 := by decide
private theorem lowerTwo_row_1158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1158 j) = 285645885 := by decide
private theorem lowerTwo_row_1159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1159 j) = 286237523 := by decide
private theorem lowerTwo_row_1160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1160 j) = 286828561 := by decide
private theorem lowerTwo_row_1161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1161 j) = 286582593 := by decide
private theorem lowerTwo_row_1162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1162 j) = 287171871 := by decide
private theorem lowerTwo_row_1163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1163 j) = 286923925 := by decide
private theorem lowerTwo_row_1164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1164 j) = 287511447 := by decide
private theorem lowerTwo_row_1165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1165 j) = 287261524 := by decide
private theorem lowerTwo_row_1166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1166 j) = 287847278 := by decide
private theorem lowerTwo_row_1167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1167 j) = 288432453 := by decide
private theorem lowerTwo_row_1168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1168 j) = 288179381 := by decide
private theorem lowerTwo_row_1169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1169 j) = 288762806 := by decide
private theorem lowerTwo_row_1170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1170 j) = 288507760 := by decide
private theorem lowerTwo_row_1171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1171 j) = 289089434 := by decide
private theorem lowerTwo_row_1172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1172 j) = 288832423 := by decide
private theorem lowerTwo_row_1173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1173 j) = 289412378 := by decide
private theorem lowerTwo_row_1174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1174 j) = 289991741 := by decide
private theorem lowerTwo_row_1175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1175 j) = 289731594 := by decide
private theorem lowerTwo_row_1176 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1176 j) = 290309241 := by decide
private theorem lowerTwo_row_1177 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1177 j) = 290047139 := by decide
private theorem lowerTwo_row_1178 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1178 j) = 290623066 := by decide
private theorem lowerTwo_row_1179 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1179 j) = 290358989 := by decide
private theorem lowerTwo_row_1180 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1180 j) = 290933188 := by decide
private theorem lowerTwo_row_1181 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1181 j) = 291506831 := by decide
private theorem lowerTwo_row_1182 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1182 j) = 291239659 := by decide
private theorem lowerTwo_row_1183 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1183 j) = 291811584 := by decide
private theorem lowerTwo_row_1184 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1184 j) = 291542459 := by decide
private theorem lowerTwo_row_1185 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1185 j) = 292112688 := by decide
private theorem lowerTwo_row_1186 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1186 j) = 291841599 := by decide
private theorem lowerTwo_row_1187 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1187 j) = 292410138 := by decide
private theorem lowerTwo_row_1188 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1188 j) = 292978098 := by decide
private theorem lowerTwo_row_1189 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1189 j) = 292703945 := by decide
private theorem lowerTwo_row_1190 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1190 j) = 293270198 := by decide
private theorem lowerTwo_row_1191 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1191 j) = 292994115 := by decide
private theorem lowerTwo_row_1192 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1192 j) = 293558695 := by decide
private theorem lowerTwo_row_1193 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1193 j) = 293280670 := by decide
private theorem lowerTwo_row_1194 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1194 j) = 293843569 := by decide
private theorem lowerTwo_row_1195 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1195 j) = 294405912 := by decide
private theorem lowerTwo_row_1196 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1196 j) = 294124830 := by decide
private theorem lowerTwo_row_1197 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1197 j) = 294685494 := by decide
private theorem lowerTwo_row_1198 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1198 j) = 294402479 := by decide
private theorem lowerTwo_row_1199 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1199 j) = 294961478 := by decide
private theorem lowerTwo_row_1200 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1200 j) = 294676538 := by decide
private theorem lowerTwo_row_1201 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1201 j) = 295233877 := by decide
private theorem lowerTwo_row_1202 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1202 j) = 295790667 := by decide
private theorem lowerTwo_row_1203 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1203 j) = 295502686 := by decide
private theorem lowerTwo_row_1204 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1204 j) = 296057825 := by decide
private theorem lowerTwo_row_1205 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1205 j) = 295767902 := by decide
private theorem lowerTwo_row_1206 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1206 j) = 296321337 := by decide
private theorem lowerTwo_row_1207 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1207 j) = 296029427 := by decide
private theorem lowerTwo_row_1208 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1208 j) = 296581105 := by decide
private theorem lowerTwo_row_1209 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1209 j) = 297132213 := by decide
private theorem lowerTwo_row_1210 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1210 j) = 296837137 := by decide
private theorem lowerTwo_row_1211 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1211 j) = 297386507 := by decide
private theorem lowerTwo_row_1212 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1212 j) = 297089435 := by decide
private theorem lowerTwo_row_1213 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1213 j) = 297637058 := by decide
private theorem lowerTwo_row_1214 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1214 j) = 297338008 := by decide
private theorem lowerTwo_row_1215 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1215 j) = 297883910 := by decide

/-- Page 51. Exact E2 row block 1152 through 1215. -/
theorem lowerTwo_rows312_18 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1152+i) j) = 18657585435 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1152, lowerTwo_row_1153, lowerTwo_row_1154, lowerTwo_row_1155, lowerTwo_row_1156, lowerTwo_row_1157, lowerTwo_row_1158, lowerTwo_row_1159, lowerTwo_row_1160, lowerTwo_row_1161, lowerTwo_row_1162, lowerTwo_row_1163, lowerTwo_row_1164, lowerTwo_row_1165, lowerTwo_row_1166, lowerTwo_row_1167, lowerTwo_row_1168, lowerTwo_row_1169, lowerTwo_row_1170, lowerTwo_row_1171, lowerTwo_row_1172, lowerTwo_row_1173, lowerTwo_row_1174, lowerTwo_row_1175, lowerTwo_row_1176, lowerTwo_row_1177, lowerTwo_row_1178, lowerTwo_row_1179, lowerTwo_row_1180, lowerTwo_row_1181, lowerTwo_row_1182, lowerTwo_row_1183, lowerTwo_row_1184, lowerTwo_row_1185, lowerTwo_row_1186, lowerTwo_row_1187, lowerTwo_row_1188, lowerTwo_row_1189, lowerTwo_row_1190, lowerTwo_row_1191, lowerTwo_row_1192, lowerTwo_row_1193, lowerTwo_row_1194, lowerTwo_row_1195, lowerTwo_row_1196, lowerTwo_row_1197, lowerTwo_row_1198, lowerTwo_row_1199, lowerTwo_row_1200, lowerTwo_row_1201, lowerTwo_row_1202, lowerTwo_row_1203, lowerTwo_row_1204, lowerTwo_row_1205, lowerTwo_row_1206, lowerTwo_row_1207, lowerTwo_row_1208, lowerTwo_row_1209, lowerTwo_row_1210, lowerTwo_row_1211, lowerTwo_row_1212, lowerTwo_row_1213, lowerTwo_row_1214, lowerTwo_row_1215, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
