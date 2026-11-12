/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1600 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1600 j) = 416611169 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1601 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1601 j) = 416951678 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1602 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1602 j) = 416821876 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1603 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1603 j) = 417684407 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1604 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1604 j) = 417553901 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1605 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1605 j) = 418374516 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1606 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1606 j) = 417803145 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1607 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1607 j) = 418623288 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1608 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1608 j) = 419443724 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1609 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1609 j) = 419352602 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1610 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1610 j) = 420172891 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1611 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1611 j) = 419556459 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1612 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1612 j) = 420417939 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1613 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1613 j) = 420283378 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1614 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1614 j) = 421102920 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1615 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1615 j) = 421964512 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1616 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1616 j) = 421344764 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1617 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1617 j) = 422164139 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1618 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1618 j) = 422068946 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1619 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1619 j) = 422888166 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1620 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1620 j) = 422750497 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1621 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1621 j) = 423126266 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1622 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1622 j) = 423945299 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1623 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1623 j) = 423806092 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1624 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1624 j) = 424666618 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1625 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1625 j) = 424526636 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1626 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1626 j) = 424859276 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1627 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1627 j) = 424759929 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1628 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1628 j) = 425578066 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1629 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1629 j) = 426396603 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1630 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1630 j) = 426295936 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1631 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1631 j) = 426627171 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1632 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1632 j) = 426483805 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1633 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1633 j) = 427343256 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1634 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1634 j) = 427199127 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1635 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1635 j) = 428016739 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1636 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1636 j) = 428388175 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1637 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1637 j) = 428242458 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1638 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1638 j) = 429059921 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1639 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1639 j) = 428955032 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1640 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1640 j) = 429772312 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1641 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1641 j) = 429135850 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1642 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1642 j) = 429994190 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1643 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1643 j) = 430811319 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1644 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1644 j) = 430662454 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1645 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1645 j) = 431520943 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1646 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1646 j) = 430881042 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1647 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1647 j) = 431697432 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1648 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1648 j) = 431588324 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1649 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1649 j) = 432404544 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1650 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1650 j) = 433221074 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1651 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1651 j) = 432619242 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1652 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1652 j) = 433435313 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1653 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1653 j) = 433282162 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1654 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1654 j) = 434139581 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1655 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1655 j) = 433985673 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1656 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1656 j) = 434308830 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1657 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1657 j) = 435166044 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1658 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1658 j) = 435010488 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1659 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1659 j) = 435825913 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1660 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1660 j) = 435711074 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1661 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1661 j) = 436032831 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1662 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1662 j) = 435875325 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1663 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1663 j) = 436731577 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1600 through 1663. -/
theorem lowerTwo_rows312_25 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1600+i) j) = 27306024859 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1600, lowerTwo_row_1601, lowerTwo_row_1602, lowerTwo_row_1603, lowerTwo_row_1604, lowerTwo_row_1605, lowerTwo_row_1606, lowerTwo_row_1607, lowerTwo_row_1608, lowerTwo_row_1609, lowerTwo_row_1610, lowerTwo_row_1611, lowerTwo_row_1612, lowerTwo_row_1613, lowerTwo_row_1614, lowerTwo_row_1615, lowerTwo_row_1616, lowerTwo_row_1617, lowerTwo_row_1618, lowerTwo_row_1619, lowerTwo_row_1620, lowerTwo_row_1621, lowerTwo_row_1622, lowerTwo_row_1623, lowerTwo_row_1624, lowerTwo_row_1625, lowerTwo_row_1626, lowerTwo_row_1627, lowerTwo_row_1628, lowerTwo_row_1629, lowerTwo_row_1630, lowerTwo_row_1631, lowerTwo_row_1632, lowerTwo_row_1633, lowerTwo_row_1634, lowerTwo_row_1635, lowerTwo_row_1636, lowerTwo_row_1637, lowerTwo_row_1638, lowerTwo_row_1639, lowerTwo_row_1640, lowerTwo_row_1641, lowerTwo_row_1642, lowerTwo_row_1643, lowerTwo_row_1644, lowerTwo_row_1645, lowerTwo_row_1646, lowerTwo_row_1647, lowerTwo_row_1648, lowerTwo_row_1649, lowerTwo_row_1650, lowerTwo_row_1651, lowerTwo_row_1652, lowerTwo_row_1653, lowerTwo_row_1654, lowerTwo_row_1655, lowerTwo_row_1656, lowerTwo_row_1657, lowerTwo_row_1658, lowerTwo_row_1659, lowerTwo_row_1660, lowerTwo_row_1661, lowerTwo_row_1662, lowerTwo_row_1663, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
