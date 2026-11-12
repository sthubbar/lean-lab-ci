/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1984 j) = 475755879 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1985 j) = 476161545 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1986 j) = 475992920 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1987 j) = 474934643 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1988 j) = 475338993 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1989 j) = 474614945 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1990 j) = 474680841 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1991 j) = 473378717 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1992 j) = 473780646 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1993 j) = 473843834 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1994 j) = 473114185 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1995 j) = 473515178 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1996 j) = 471865842 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1997 j) = 472265298 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1998 j) = 471531238 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1999 j) = 471588199 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2000 j) = 471986727 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2001 j) = 470670437 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2002 j) = 470724630 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2003 j) = 469984848 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2004 j) = 470380871 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2005 j) = 469294845 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2006 j) = 469109180 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2007 j) = 469503801 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2008 j) = 468412733 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2009 j) = 468806185 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2010 j) = 468058705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2011 j) = 467522045 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2012 j) = 466771959 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2013 j) = 467162888 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2014 j) = 467205473 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2015 j) = 466452140 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2016 j) = 466258468 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2017 j) = 465152980 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2018 j) = 465541295 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2019 j) = 464783509 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2020 j) = 464819770 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2021 j) = 464621973 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2022 j) = 463860456 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2023 j) = 463893932 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2024 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2024 j) = 463130262 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2025 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2025 j) = 463515043 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2026 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2026 j) = 461808855 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2027 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2027 j) = 462192030 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2028 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2028 j) = 462575395 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2029 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2029 j) = 461450814 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2030 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2030 j) = 461832960 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2031 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2031 j) = 460472978 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2032 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2032 j) = 460497252 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2033 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2033 j) = 459722951 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2034 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2034 j) = 460102413 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2035 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2035 j) = 460124311 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2036 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2036 j) = 458756682 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2037 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2037 j) = 459134680 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2038 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2038 j) = 457995355 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2039 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2039 j) = 458372108 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2040 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2040 j) = 457589681 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2041 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2041 j) = 457013392 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2042 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2042 j) = 457388613 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2043 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2043 j) = 456602311 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2044 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2044 j) = 456614595 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2045 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2045 j) = 455825976 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2046 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2046 j) = 455605857 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2047 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2047 j) = 454451439 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 1984 through 2047. -/
theorem lowerTwo_rows312_31 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1984+i) j) = 29826118706 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1984, lowerTwo_row_1985, lowerTwo_row_1986, lowerTwo_row_1987, lowerTwo_row_1988, lowerTwo_row_1989, lowerTwo_row_1990, lowerTwo_row_1991, lowerTwo_row_1992, lowerTwo_row_1993, lowerTwo_row_1994, lowerTwo_row_1995, lowerTwo_row_1996, lowerTwo_row_1997, lowerTwo_row_1998, lowerTwo_row_1999, lowerTwo_row_2000, lowerTwo_row_2001, lowerTwo_row_2002, lowerTwo_row_2003, lowerTwo_row_2004, lowerTwo_row_2005, lowerTwo_row_2006, lowerTwo_row_2007, lowerTwo_row_2008, lowerTwo_row_2009, lowerTwo_row_2010, lowerTwo_row_2011, lowerTwo_row_2012, lowerTwo_row_2013, lowerTwo_row_2014, lowerTwo_row_2015, lowerTwo_row_2016, lowerTwo_row_2017, lowerTwo_row_2018, lowerTwo_row_2019, lowerTwo_row_2020, lowerTwo_row_2021, lowerTwo_row_2022, lowerTwo_row_2023, lowerTwo_row_2024, lowerTwo_row_2025, lowerTwo_row_2026, lowerTwo_row_2027, lowerTwo_row_2028, lowerTwo_row_2029, lowerTwo_row_2030, lowerTwo_row_2031, lowerTwo_row_2032, lowerTwo_row_2033, lowerTwo_row_2034, lowerTwo_row_2035, lowerTwo_row_2036, lowerTwo_row_2037, lowerTwo_row_2038, lowerTwo_row_2039, lowerTwo_row_2040, lowerTwo_row_2041, lowerTwo_row_2042, lowerTwo_row_2043, lowerTwo_row_2044, lowerTwo_row_2045, lowerTwo_row_2046, lowerTwo_row_2047, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
