/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1536 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1536 j) = 393996592 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1537 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1537 j) = 394865552 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1538 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1538 j) = 395692847 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1539 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1539 j) = 395590505 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1540 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1540 j) = 396459559 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1541 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1541 j) = 395887621 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1542 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1542 j) = 396714205 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1543 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1543 j) = 396652192 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1544 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1544 j) = 397478602 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1545 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1545 j) = 398305284 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1546 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1546 j) = 397772180 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1547 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1547 j) = 398598412 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1548 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1548 j) = 398492215 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1549 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1549 j) = 399360181 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1550 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1550 j) = 399253348 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1551 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1551 j) = 399608288 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1552 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1552 j) = 400476058 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1553 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1553 j) = 400367719 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1554 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1554 j) = 401193334 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1555 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1555 j) = 401126232 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1556 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1556 j) = 401479847 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1557 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1557 j) = 401369822 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1558 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1558 j) = 402236680 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1559 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1559 j) = 403061937 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1560 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1560 j) = 402950731 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1561 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1561 j) = 403344886 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1562 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1562 j) = 403232688 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1563 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1563 j) = 404057259 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1564 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1564 j) = 403986193 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1565 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1565 j) = 404810598 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1566 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1566 j) = 405161530 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1567 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1567 j) = 405088950 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1568 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1568 j) = 405913181 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1569 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1569 j) = 405798039 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1570 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1570 j) = 406663889 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1571 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1571 j) = 406073340 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1572 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1572 j) = 406896842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1573 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1573 j) = 407762510 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1574 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1574 j) = 407645194 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1575 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1575 j) = 408468784 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1576 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1576 j) = 407916855 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1577 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1577 j) = 408740026 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1578 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1578 j) = 408620941 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1579 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1579 j) = 409485726 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1580 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1580 j) = 410309008 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1581 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1581 j) = 409711975 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1582 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1582 j) = 410576584 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1583 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1583 j) = 410455294 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1584 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1584 j) = 411277858 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1585 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1585 j) = 411197662 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1586 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1586 j) = 411542313 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1587 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1587 j) = 412364739 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1588 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1588 j) = 412282991 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1589 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1589 j) = 413105208 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1590 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1590 j) = 412980955 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1591 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1591 j) = 413366018 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1592 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1592 j) = 413240735 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1593 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1593 j) = 414062280 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1594 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1594 j) = 414925909 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1595 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1595 j) = 414799389 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1596 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1596 j) = 415141311 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1597 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1597 j) = 415055518 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1598 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1598 j) = 415876692 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1599 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1599 j) = 415748441 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1536 through 1599. -/
theorem lowerTwo_rows312_24 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1536+i) j) = 25946678254 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1536, lowerTwo_row_1537, lowerTwo_row_1538, lowerTwo_row_1539, lowerTwo_row_1540, lowerTwo_row_1541, lowerTwo_row_1542, lowerTwo_row_1543, lowerTwo_row_1544, lowerTwo_row_1545, lowerTwo_row_1546, lowerTwo_row_1547, lowerTwo_row_1548, lowerTwo_row_1549, lowerTwo_row_1550, lowerTwo_row_1551, lowerTwo_row_1552, lowerTwo_row_1553, lowerTwo_row_1554, lowerTwo_row_1555, lowerTwo_row_1556, lowerTwo_row_1557, lowerTwo_row_1558, lowerTwo_row_1559, lowerTwo_row_1560, lowerTwo_row_1561, lowerTwo_row_1562, lowerTwo_row_1563, lowerTwo_row_1564, lowerTwo_row_1565, lowerTwo_row_1566, lowerTwo_row_1567, lowerTwo_row_1568, lowerTwo_row_1569, lowerTwo_row_1570, lowerTwo_row_1571, lowerTwo_row_1572, lowerTwo_row_1573, lowerTwo_row_1574, lowerTwo_row_1575, lowerTwo_row_1576, lowerTwo_row_1577, lowerTwo_row_1578, lowerTwo_row_1579, lowerTwo_row_1580, lowerTwo_row_1581, lowerTwo_row_1582, lowerTwo_row_1583, lowerTwo_row_1584, lowerTwo_row_1585, lowerTwo_row_1586, lowerTwo_row_1587, lowerTwo_row_1588, lowerTwo_row_1589, lowerTwo_row_1590, lowerTwo_row_1591, lowerTwo_row_1592, lowerTwo_row_1593, lowerTwo_row_1594, lowerTwo_row_1595, lowerTwo_row_1596, lowerTwo_row_1597, lowerTwo_row_1598, lowerTwo_row_1599, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
