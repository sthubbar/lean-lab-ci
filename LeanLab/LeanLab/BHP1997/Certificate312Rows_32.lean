/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2048 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2048 j) = 453659220 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2049 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2049 j) = 452866151 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2050 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2050 j) = 452870267 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2051 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2051 j) = 452644239 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2052 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2052 j) = 453012658 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2053 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2053 j) = 453015166 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2054 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2054 j) = 453383658 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2055 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2055 j) = 453752305 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2056 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2056 j) = 453157266 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2057 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2057 j) = 453525540 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2058 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2058 j) = 453893956 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2059 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2059 j) = 453893610 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2060 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2060 j) = 454262118 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2061 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2061 j) = 454032758 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2062 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2062 j) = 454030787 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2063 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2063 j) = 454399054 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2064 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2064 j) = 454767431 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2065 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2065 j) = 454764275 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2066 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2066 j) = 454533146 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2067 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2067 j) = 454901295 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2068 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2068 j) = 454896479 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2069 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2069 j) = 455264716 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2070 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2070 j) = 455633100 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2071 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2071 j) = 455025781 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2072 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2072 j) = 455393783 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2073 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2073 j) = 455761926 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2074 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2074 j) = 455754227 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2075 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2075 j) = 456122454 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2076 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2076 j) = 455887840 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2077 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2077 j) = 455878425 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2078 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2078 j) = 456246411 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2079 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2079 j) = 456614566 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2080 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2080 j) = 456603909 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2081 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2081 j) = 456367447 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2082 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2082 j) = 456735424 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2083 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2083 j) = 456723143 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2084 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2084 j) = 457091136 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2085 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2085 j) = 457459391 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2086 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2086 j) = 456839649 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2087 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2087 j) = 457207465 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2088 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2088 j) = 457575516 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2089 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2089 j) = 457560536 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2090 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2090 j) = 457928688 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2091 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2091 j) = 457688921 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2092 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2092 j) = 457672329 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2093 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2093 j) = 458040290 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2094 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2094 j) = 458408384 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2095 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2095 j) = 458390667 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2096 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2096 j) = 458149120 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2097 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2097 j) = 458517042 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2098 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2098 j) = 458497705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2099 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2099 j) = 458865749 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2100 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2100 j) = 459233939 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2101 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2101 j) = 458601951 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2102 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2102 j) = 458969776 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2103 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2103 j) = 459337787 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2104 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2104 j) = 459315698 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2105 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2105 j) = 459683792 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2106 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2106 j) = 459438798 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2107 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2107 j) = 459415076 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2108 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2108 j) = 459782966 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2109 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2109 j) = 460151042 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2110 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2110 j) = 460126130 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2111 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2111 j) = 459879269 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 2048 through 2111. -/
theorem lowerTwo_rows312_32 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2048+i) j) = 29210103343 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2048, lowerTwo_row_2049, lowerTwo_row_2050, lowerTwo_row_2051, lowerTwo_row_2052, lowerTwo_row_2053, lowerTwo_row_2054, lowerTwo_row_2055, lowerTwo_row_2056, lowerTwo_row_2057, lowerTwo_row_2058, lowerTwo_row_2059, lowerTwo_row_2060, lowerTwo_row_2061, lowerTwo_row_2062, lowerTwo_row_2063, lowerTwo_row_2064, lowerTwo_row_2065, lowerTwo_row_2066, lowerTwo_row_2067, lowerTwo_row_2068, lowerTwo_row_2069, lowerTwo_row_2070, lowerTwo_row_2071, lowerTwo_row_2072, lowerTwo_row_2073, lowerTwo_row_2074, lowerTwo_row_2075, lowerTwo_row_2076, lowerTwo_row_2077, lowerTwo_row_2078, lowerTwo_row_2079, lowerTwo_row_2080, lowerTwo_row_2081, lowerTwo_row_2082, lowerTwo_row_2083, lowerTwo_row_2084, lowerTwo_row_2085, lowerTwo_row_2086, lowerTwo_row_2087, lowerTwo_row_2088, lowerTwo_row_2089, lowerTwo_row_2090, lowerTwo_row_2091, lowerTwo_row_2092, lowerTwo_row_2093, lowerTwo_row_2094, lowerTwo_row_2095, lowerTwo_row_2096, lowerTwo_row_2097, lowerTwo_row_2098, lowerTwo_row_2099, lowerTwo_row_2100, lowerTwo_row_2101, lowerTwo_row_2102, lowerTwo_row_2103, lowerTwo_row_2104, lowerTwo_row_2105, lowerTwo_row_2106, lowerTwo_row_2107, lowerTwo_row_2108, lowerTwo_row_2109, lowerTwo_row_2110, lowerTwo_row_2111, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
