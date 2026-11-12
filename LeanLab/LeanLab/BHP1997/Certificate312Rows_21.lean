/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1344 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1344 j) = 317856132 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1345 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1345 j) = 317857309 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1346 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1346 j) = 318298842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1347 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1347 j) = 318297898 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1348 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1348 j) = 319171283 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1349 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1349 j) = 320044259 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1350 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1350 j) = 320040333 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1351 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1351 j) = 320477254 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1352 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1352 j) = 320471193 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1353 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1353 j) = 321340848 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1354 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1354 j) = 321332928 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1355 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1355 j) = 322201090 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1356 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1356 j) = 322633474 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1357 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1357 j) = 322622326 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1358 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1358 j) = 323488285 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1359 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1359 j) = 323475280 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1360 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1360 j) = 324339772 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1361 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1361 j) = 323888687 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1362 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1362 j) = 324751380 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1363 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1363 j) = 325613710 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1364 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1364 j) = 325638499 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1365 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1365 j) = 326542423 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1366 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1366 j) = 326171543 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1367 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1367 j) = 327074187 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1368 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1368 j) = 327096017 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1369 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1369 j) = 328040429 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1370 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1370 j) = 328941947 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1371 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1371 j) = 328523587 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1372 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1372 j) = 329466588 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1373 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1373 j) = 329484612 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1374 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1374 j) = 330383891 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1375 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1375 j) = 330443311 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1376 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1376 j) = 330902745 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1377 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1377 j) = 331800604 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1378 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1378 j) = 331857567 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1379 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1379 j) = 332754473 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1380 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1380 j) = 332767354 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1381 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1381 j) = 333266242 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1382 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1382 j) = 333277543 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1383 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1383 j) = 334172243 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1384 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1384 j) = 335109495 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1385 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1385 j) = 335118627 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1386 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1386 j) = 335571574 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1387 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1387 j) = 335621752 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1388 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1388 j) = 336514105 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1389 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1389 j) = 336520266 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1390 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1390 j) = 337454275 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1391 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1391 j) = 337904046 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1392 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1392 j) = 337907751 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1393 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1393 j) = 338840398 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1394 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1394 j) = 338842754 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1395 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1395 j) = 339731768 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1396 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1396 j) = 339333099 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1397 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1397 j) = 340220913 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1398 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1398 j) = 341108571 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1399 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1399 j) = 341149748 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1400 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1400 j) = 342036458 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1401 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1401 j) = 341590536 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1402 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1402 j) = 342518624 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1403 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1403 j) = 342514249 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1404 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1404 j) = 343398758 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1405 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1405 j) = 344325736 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1406 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1406 j) = 343875214 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1407 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1407 j) = 344758388 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1344 through 1407. -/
theorem lowerTwo_rows312_21 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1344+i) j) = 21178775193 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1344, lowerTwo_row_1345, lowerTwo_row_1346, lowerTwo_row_1347, lowerTwo_row_1348, lowerTwo_row_1349, lowerTwo_row_1350, lowerTwo_row_1351, lowerTwo_row_1352, lowerTwo_row_1353, lowerTwo_row_1354, lowerTwo_row_1355, lowerTwo_row_1356, lowerTwo_row_1357, lowerTwo_row_1358, lowerTwo_row_1359, lowerTwo_row_1360, lowerTwo_row_1361, lowerTwo_row_1362, lowerTwo_row_1363, lowerTwo_row_1364, lowerTwo_row_1365, lowerTwo_row_1366, lowerTwo_row_1367, lowerTwo_row_1368, lowerTwo_row_1369, lowerTwo_row_1370, lowerTwo_row_1371, lowerTwo_row_1372, lowerTwo_row_1373, lowerTwo_row_1374, lowerTwo_row_1375, lowerTwo_row_1376, lowerTwo_row_1377, lowerTwo_row_1378, lowerTwo_row_1379, lowerTwo_row_1380, lowerTwo_row_1381, lowerTwo_row_1382, lowerTwo_row_1383, lowerTwo_row_1384, lowerTwo_row_1385, lowerTwo_row_1386, lowerTwo_row_1387, lowerTwo_row_1388, lowerTwo_row_1389, lowerTwo_row_1390, lowerTwo_row_1391, lowerTwo_row_1392, lowerTwo_row_1393, lowerTwo_row_1394, lowerTwo_row_1395, lowerTwo_row_1396, lowerTwo_row_1397, lowerTwo_row_1398, lowerTwo_row_1399, lowerTwo_row_1400, lowerTwo_row_1401, lowerTwo_row_1402, lowerTwo_row_1403, lowerTwo_row_1404, lowerTwo_row_1405, lowerTwo_row_1406, lowerTwo_row_1407, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
