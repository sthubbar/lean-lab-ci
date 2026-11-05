/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_27
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1792 j) = 474552217 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1793 j) = 474325411 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1794 j) = 475125327 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1795 j) = 474938724 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1796 j) = 475213956 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1797 j) = 476013618 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1798 j) = 475825026 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1799 j) = 476624448 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1800 j) = 476393725 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1801 j) = 476708317 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1802 j) = 476476202 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1803 j) = 477274716 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1804 j) = 478114675 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1805 j) = 477880908 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1806 j) = 478152614 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1807 j) = 477958575 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1808 j) = 478756499 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1809 j) = 478520271 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1810 j) = 479358970 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1811 j) = 479628947 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1812 j) = 479390682 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1813 j) = 480229092 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1814 j) = 479989807 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1815 j) = 480786811 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1816 j) = 480058359 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1817 j) = 480854743 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1818 j) = 481651450 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1819 j) = 481450104 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1820 j) = 482246540 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1821 j) = 481472643 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1822 j) = 482309487 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1823 j) = 482064582 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1824 j) = 482860012 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1825 j) = 483696907 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1826 j) = 482918658 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1827 j) = 483713791 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1828 j) = 483506814 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1829 j) = 484301625 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1830 j) = 484052474 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1831 j) = 484355240 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1832 j) = 485149744 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1833 j) = 484898481 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1834 j) = 485733748 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1835 j) = 485481390 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1836 j) = 485741232 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1837 j) = 485528523 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1838 j) = 486321708 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1839 j) = 487115238 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1840 j) = 486900712 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1841 j) = 487158674 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1842 j) = 486901664 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1843 j) = 487735228 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1844 j) = 487477137 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1845 j) = 488269295 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1846 j) = 488566437 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1847 j) = 488306153 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1848 j) = 489098032 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1849 j) = 488877632 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1850 j) = 489669173 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1851 j) = 488868957 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1852 j) = 489700795 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1853 j) = 490492032 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1854 j) = 490227301 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1855 j) = 491059165 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 1792 through 1855. -/
theorem lowerTwo_rows312_28 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1792+i) j) = 30885031418 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1792, lowerTwo_row_1793, lowerTwo_row_1794, lowerTwo_row_1795, lowerTwo_row_1796, lowerTwo_row_1797, lowerTwo_row_1798, lowerTwo_row_1799, lowerTwo_row_1800, lowerTwo_row_1801, lowerTwo_row_1802, lowerTwo_row_1803, lowerTwo_row_1804, lowerTwo_row_1805, lowerTwo_row_1806, lowerTwo_row_1807, lowerTwo_row_1808, lowerTwo_row_1809, lowerTwo_row_1810, lowerTwo_row_1811, lowerTwo_row_1812, lowerTwo_row_1813, lowerTwo_row_1814, lowerTwo_row_1815, lowerTwo_row_1816, lowerTwo_row_1817, lowerTwo_row_1818, lowerTwo_row_1819, lowerTwo_row_1820, lowerTwo_row_1821, lowerTwo_row_1822, lowerTwo_row_1823, lowerTwo_row_1824, lowerTwo_row_1825, lowerTwo_row_1826, lowerTwo_row_1827, lowerTwo_row_1828, lowerTwo_row_1829, lowerTwo_row_1830, lowerTwo_row_1831, lowerTwo_row_1832, lowerTwo_row_1833, lowerTwo_row_1834, lowerTwo_row_1835, lowerTwo_row_1836, lowerTwo_row_1837, lowerTwo_row_1838, lowerTwo_row_1839, lowerTwo_row_1840, lowerTwo_row_1841, lowerTwo_row_1842, lowerTwo_row_1843, lowerTwo_row_1844, lowerTwo_row_1845, lowerTwo_row_1846, lowerTwo_row_1847, lowerTwo_row_1848, lowerTwo_row_1849, lowerTwo_row_1850, lowerTwo_row_1851, lowerTwo_row_1852, lowerTwo_row_1853, lowerTwo_row_1854, lowerTwo_row_1855, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
