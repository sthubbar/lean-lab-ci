/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1280 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1280 j) = 307783376 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1281 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1281 j) = 308277129 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1282 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1282 j) = 307909883 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1283 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1283 j) = 308401947 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1284 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1284 j) = 308032693 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1285 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1285 j) = 308523098 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1286 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1286 j) = 309012961 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1287 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1287 j) = 308640599 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1288 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1288 j) = 309128794 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1289 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1289 j) = 308754437 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1290 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1290 j) = 309240980 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1291 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1291 j) = 308864655 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1292 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1292 j) = 309349538 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1293 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1293 j) = 309833895 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1294 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1294 j) = 309454448 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1295 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1295 j) = 309937168 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1296 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1296 j) = 309555753 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1297 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1297 j) = 310036813 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1298 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1298 j) = 309653435 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1299 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1299 j) = 310132832 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1300 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1300 j) = 310611745 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1301 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1301 j) = 310225278 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1302 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1302 j) = 310702541 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1303 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1303 j) = 310314095 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1304 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1304 j) = 310789721 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1305 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1305 j) = 310399320 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1306 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1306 j) = 310873329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1307 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1307 j) = 311346821 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1308 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1308 j) = 310953332 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1309 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1309 j) = 311425217 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1310 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1310 j) = 311029768 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1311 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1311 j) = 311500031 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1312 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1312 j) = 311102637 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1313 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1313 j) = 311571277 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1314 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1314 j) = 312039411 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1315 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1315 j) = 311638959 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1316 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1316 j) = 312105475 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1317 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1317 j) = 311703083 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1318 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1318 j) = 312168000 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1319 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1319 j) = 311763667 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1320 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1320 j) = 312226970 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1321 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1321 j) = 312689807 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1322 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1322 j) = 312282401 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1323 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1323 j) = 312743638 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1324 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1324 j) = 312334301 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1325 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1325 j) = 312793925 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1326 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1326 j) = 312382686 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1327 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1327 j) = 312840709 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1328 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1328 j) = 313298275 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1329 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1329 j) = 312883973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1330 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1330 j) = 313339939 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1331 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1331 j) = 312923717 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1332 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1332 j) = 313378093 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1333 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1333 j) = 312959890 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1334 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1334 j) = 313412585 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1335 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1335 j) = 314296460 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1336 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1336 j) = 313874864 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1337 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1337 j) = 314756918 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1338 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1338 j) = 314765134 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1339 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1339 j) = 315645628 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1340 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1340 j) = 315651939 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1341 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1341 j) = 316098088 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1342 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1342 j) = 316976354 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1343 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1343 j) = 316979417 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1280 through 1343. -/
theorem lowerTwo_rows312_20 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1280+i) j) = 19936323852 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1280, lowerTwo_row_1281, lowerTwo_row_1282, lowerTwo_row_1283, lowerTwo_row_1284, lowerTwo_row_1285, lowerTwo_row_1286, lowerTwo_row_1287, lowerTwo_row_1288, lowerTwo_row_1289, lowerTwo_row_1290, lowerTwo_row_1291, lowerTwo_row_1292, lowerTwo_row_1293, lowerTwo_row_1294, lowerTwo_row_1295, lowerTwo_row_1296, lowerTwo_row_1297, lowerTwo_row_1298, lowerTwo_row_1299, lowerTwo_row_1300, lowerTwo_row_1301, lowerTwo_row_1302, lowerTwo_row_1303, lowerTwo_row_1304, lowerTwo_row_1305, lowerTwo_row_1306, lowerTwo_row_1307, lowerTwo_row_1308, lowerTwo_row_1309, lowerTwo_row_1310, lowerTwo_row_1311, lowerTwo_row_1312, lowerTwo_row_1313, lowerTwo_row_1314, lowerTwo_row_1315, lowerTwo_row_1316, lowerTwo_row_1317, lowerTwo_row_1318, lowerTwo_row_1319, lowerTwo_row_1320, lowerTwo_row_1321, lowerTwo_row_1322, lowerTwo_row_1323, lowerTwo_row_1324, lowerTwo_row_1325, lowerTwo_row_1326, lowerTwo_row_1327, lowerTwo_row_1328, lowerTwo_row_1329, lowerTwo_row_1330, lowerTwo_row_1331, lowerTwo_row_1332, lowerTwo_row_1333, lowerTwo_row_1334, lowerTwo_row_1335, lowerTwo_row_1336, lowerTwo_row_1337, lowerTwo_row_1338, lowerTwo_row_1339, lowerTwo_row_1340, lowerTwo_row_1341, lowerTwo_row_1342, lowerTwo_row_1343, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
