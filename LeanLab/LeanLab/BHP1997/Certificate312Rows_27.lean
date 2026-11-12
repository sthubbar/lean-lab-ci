/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1728 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1728 j) = 456226519 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1729 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1729 j) = 457075727 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1730 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1730 j) = 456883956 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1731 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1731 j) = 457182734 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1732 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1732 j) = 457031069 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1733 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1733 j) = 457838130 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1734 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1734 j) = 458645582 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1735 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1735 j) = 458492424 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1736 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1736 j) = 458789640 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1737 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1737 j) = 458593936 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1738 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1738 j) = 459441871 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1739 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1739 j) = 459245276 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1740 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1740 j) = 460051696 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1741 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1741 j) = 460388559 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1742 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1742 j) = 460190184 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1743 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1743 j) = 460996384 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1744 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1744 j) = 460838320 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1745 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1745 j) = 461644333 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1746 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1746 j) = 460931778 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1747 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1747 j) = 461778419 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1748 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1748 j) = 462584199 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1749 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1749 j) = 462382114 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1750 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1750 j) = 463228916 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1751 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1751 j) = 462512465 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1752 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1752 j) = 463317376 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1753 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1753 j) = 463154429 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1754 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1754 j) = 463959118 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1755 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1755 j) = 464764193 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1756 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1756 j) = 464085010 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1757 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1757 j) = 464889506 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1758 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1758 j) = 464682471 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1759 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1759 j) = 465527992 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1760 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1760 j) = 465320056 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1761 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1761 j) = 465608162 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1762 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1762 j) = 466453456 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1763 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1763 j) = 466243637 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1764 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1764 j) = 467047425 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1765 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1765 j) = 466877917 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1766 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1766 j) = 467164382 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1767 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1767 j) = 466952370 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1768 j) = 467796545 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1769 j) = 468599847 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1770 j) = 468386296 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1771 j) = 468712289 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1772 j) = 468497433 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1773 j) = 469299916 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1774 j) = 469125307 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1775 j) = 469927552 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1776 j) = 470210678 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1777 j) = 470034123 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1778 j) = 470836143 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1779 j) = 470617475 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1780 j) = 471460407 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1781 j) = 470720061 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1782 j) = 471521210 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1783 j) = 472363935 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1784 j) = 472142367 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1785 j) = 472943634 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1786 j) = 472240325 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1787 j) = 473041015 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1788 j) = 472817144 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1789 j) = 473658750 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1790 j) = 474459524 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1791 j) = 473710840 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1728 through 1791. -/
theorem lowerTwo_rows312_27 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1728+i) j) = 29782144547 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1728, lowerTwo_row_1729, lowerTwo_row_1730, lowerTwo_row_1731, lowerTwo_row_1732, lowerTwo_row_1733, lowerTwo_row_1734, lowerTwo_row_1735, lowerTwo_row_1736, lowerTwo_row_1737, lowerTwo_row_1738, lowerTwo_row_1739, lowerTwo_row_1740, lowerTwo_row_1741, lowerTwo_row_1742, lowerTwo_row_1743, lowerTwo_row_1744, lowerTwo_row_1745, lowerTwo_row_1746, lowerTwo_row_1747, lowerTwo_row_1748, lowerTwo_row_1749, lowerTwo_row_1750, lowerTwo_row_1751, lowerTwo_row_1752, lowerTwo_row_1753, lowerTwo_row_1754, lowerTwo_row_1755, lowerTwo_row_1756, lowerTwo_row_1757, lowerTwo_row_1758, lowerTwo_row_1759, lowerTwo_row_1760, lowerTwo_row_1761, lowerTwo_row_1762, lowerTwo_row_1763, lowerTwo_row_1764, lowerTwo_row_1765, lowerTwo_row_1766, lowerTwo_row_1767, lowerTwo_row_1768, lowerTwo_row_1769, lowerTwo_row_1770, lowerTwo_row_1771, lowerTwo_row_1772, lowerTwo_row_1773, lowerTwo_row_1774, lowerTwo_row_1775, lowerTwo_row_1776, lowerTwo_row_1777, lowerTwo_row_1778, lowerTwo_row_1779, lowerTwo_row_1780, lowerTwo_row_1781, lowerTwo_row_1782, lowerTwo_row_1783, lowerTwo_row_1784, lowerTwo_row_1785, lowerTwo_row_1786, lowerTwo_row_1787, lowerTwo_row_1788, lowerTwo_row_1789, lowerTwo_row_1790, lowerTwo_row_1791, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
