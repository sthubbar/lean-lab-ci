/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1216 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1216 j) = 298429250 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1217 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1217 j) = 298127034 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1218 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1218 j) = 298670655 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1219 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1219 j) = 298366455 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1220 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1220 j) = 298908358 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1221 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1221 j) = 298602182 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1222 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1222 j) = 299142376 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1223 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1223 j) = 299681995 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1224 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1224 j) = 299372691 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1225 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1225 j) = 299910628 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1226 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1226 j) = 299599343 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1227 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1227 j) = 300135571 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1228 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1228 j) = 299822305 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1229 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1229 j) = 300356863 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1230 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1230 j) = 300890857 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1231 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1231 j) = 300574474 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1232 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1232 j) = 301106775 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1233 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1233 j) = 300788454 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1234 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1234 j) = 301319075 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1235 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1235 j) = 300998791 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1236 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1236 j) = 301527714 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1237 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1237 j) = 302056108 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1238 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1238 j) = 301732739 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1239 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1239 j) = 302259451 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1240 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1240 j) = 301934127 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1241 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1241 j) = 302459183 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1242 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1242 j) = 302131922 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1243 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1243 j) = 302655300 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1244 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1244 j) = 303178163 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1245 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1245 j) = 302847820 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1246 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1246 j) = 303369023 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1247 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1247 j) = 303036733 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1248 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1248 j) = 303556276 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1249 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1249 j) = 303222059 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1250 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1250 j) = 303739964 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1251 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1251 j) = 304257328 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1252 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1252 j) = 303920060 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1253 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1253 j) = 304435804 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1254 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1254 j) = 304096592 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1255 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1255 j) = 304610696 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1256 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1256 j) = 304269595 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1257 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1257 j) = 304782072 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1258 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1258 j) = 305294036 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1259 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1259 j) = 304949882 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1260 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1260 j) = 305460229 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1261 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1261 j) = 305114153 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1262 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1262 j) = 305622883 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1263 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1263 j) = 305274894 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1264 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1264 j) = 305782006 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1265 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1265 j) = 306288634 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1266 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1266 j) = 305937621 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1267 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1267 j) = 306442619 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1268 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1268 j) = 306089658 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1269 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1269 j) = 306592971 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1270 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1270 j) = 306237982 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1271 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1271 j) = 306739585 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1272 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1272 j) = 307240634 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1273 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1273 j) = 306882490 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1274 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1274 j) = 307381847 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1275 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1275 j) = 307021725 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1276 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1276 j) = 307519377 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1277 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1277 j) = 307157249 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1278 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1278 j) = 307653220 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1279 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1279 j) = 308148655 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1216 through 1279. -/
theorem lowerTwo_rows312_19 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1216+i) j) = 19405715211 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1216, lowerTwo_row_1217, lowerTwo_row_1218, lowerTwo_row_1219, lowerTwo_row_1220, lowerTwo_row_1221, lowerTwo_row_1222, lowerTwo_row_1223, lowerTwo_row_1224, lowerTwo_row_1225, lowerTwo_row_1226, lowerTwo_row_1227, lowerTwo_row_1228, lowerTwo_row_1229, lowerTwo_row_1230, lowerTwo_row_1231, lowerTwo_row_1232, lowerTwo_row_1233, lowerTwo_row_1234, lowerTwo_row_1235, lowerTwo_row_1236, lowerTwo_row_1237, lowerTwo_row_1238, lowerTwo_row_1239, lowerTwo_row_1240, lowerTwo_row_1241, lowerTwo_row_1242, lowerTwo_row_1243, lowerTwo_row_1244, lowerTwo_row_1245, lowerTwo_row_1246, lowerTwo_row_1247, lowerTwo_row_1248, lowerTwo_row_1249, lowerTwo_row_1250, lowerTwo_row_1251, lowerTwo_row_1252, lowerTwo_row_1253, lowerTwo_row_1254, lowerTwo_row_1255, lowerTwo_row_1256, lowerTwo_row_1257, lowerTwo_row_1258, lowerTwo_row_1259, lowerTwo_row_1260, lowerTwo_row_1261, lowerTwo_row_1262, lowerTwo_row_1263, lowerTwo_row_1264, lowerTwo_row_1265, lowerTwo_row_1266, lowerTwo_row_1267, lowerTwo_row_1268, lowerTwo_row_1269, lowerTwo_row_1270, lowerTwo_row_1271, lowerTwo_row_1272, lowerTwo_row_1273, lowerTwo_row_1274, lowerTwo_row_1275, lowerTwo_row_1276, lowerTwo_row_1277, lowerTwo_row_1278, lowerTwo_row_1279, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
