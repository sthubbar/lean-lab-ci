/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_32
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_2112 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2112 j) = 460247154 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2113 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2113 j) = 460179906 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2114 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2114 j) = 460547839 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2115 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2115 j) = 460915956 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2116 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2116 j) = 460230671 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2117 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2117 j) = 460598335 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2118 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2118 j) = 460966190 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2119 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2119 j) = 460895975 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2120 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2120 j) = 461263859 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2121 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2121 j) = 461013398 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2122 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2122 j) = 460941447 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2123 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2123 j) = 461309075 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2124 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2124 j) = 461676898 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2125 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2125 j) = 461603683 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2126 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2126 j) = 461351187 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2127 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2127 j) = 461718743 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2128 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2128 j) = 461643738 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2129 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2129 j) = 462011355 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2130 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2130 j) = 462379134 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2131 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2131 j) = 461680707 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2132 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2132 j) = 462048035 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2133 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2133 j) = 462415576 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2134 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2134 j) = 462337531 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2135 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2135 j) = 462705093 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2136 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2136 j) = 462448848 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2137 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2137 j) = 462369021 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2138 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2138 j) = 462736310 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2139 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2139 j) = 463103775 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2140 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2140 j) = 463022649 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2141 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2141 j) = 462764336 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2142 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2142 j) = 463131529 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2143 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2143 j) = 463048610 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2144 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2144 j) = 463415882 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2145 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2145 j) = 463783345 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2146 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2146 j) = 463071560 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2147 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2147 j) = 463438593 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2148 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2148 j) = 463805842 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2149 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2149 j) = 463720008 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2150 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2150 j) = 464087337 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2151 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2151 j) = 463825342 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2152 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2152 j) = 463737792 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2153 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2153 j) = 464104868 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2154 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2154 j) = 464472209 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2155 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2155 j) = 464383423 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2156 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2156 j) = 464119406 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2157 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2157 j) = 464486501 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2158 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2158 j) = 464395998 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2159 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2159 j) = 464763162 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2160 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2160 j) = 465130498 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2161 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2161 j) = 464405510 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2162 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2162 j) = 464772423 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2163 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2163 j) = 465139563 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2164 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2164 j) = 465046067 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2165 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2165 j) = 465413274 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2166 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2166 j) = 465145505 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2167 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2167 j) = 465050262 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2168 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2168 j) = 465417240 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2169 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2169 j) = 465784402 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2170 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2170 j) = 465687872 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2171 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2171 j) = 465418073 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2172 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2172 j) = 465784978 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2173 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2173 j) = 465686689 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2174 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2174 j) = 466053666 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_2175 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 2175 j) = 466420891 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 2112 through 2175. -/
theorem lowerTwo_rows312_33 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (2112+i) j) = 29645274744 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_2112, lowerTwo_row_2113, lowerTwo_row_2114, lowerTwo_row_2115, lowerTwo_row_2116, lowerTwo_row_2117, lowerTwo_row_2118, lowerTwo_row_2119, lowerTwo_row_2120, lowerTwo_row_2121, lowerTwo_row_2122, lowerTwo_row_2123, lowerTwo_row_2124, lowerTwo_row_2125, lowerTwo_row_2126, lowerTwo_row_2127, lowerTwo_row_2128, lowerTwo_row_2129, lowerTwo_row_2130, lowerTwo_row_2131, lowerTwo_row_2132, lowerTwo_row_2133, lowerTwo_row_2134, lowerTwo_row_2135, lowerTwo_row_2136, lowerTwo_row_2137, lowerTwo_row_2138, lowerTwo_row_2139, lowerTwo_row_2140, lowerTwo_row_2141, lowerTwo_row_2142, lowerTwo_row_2143, lowerTwo_row_2144, lowerTwo_row_2145, lowerTwo_row_2146, lowerTwo_row_2147, lowerTwo_row_2148, lowerTwo_row_2149, lowerTwo_row_2150, lowerTwo_row_2151, lowerTwo_row_2152, lowerTwo_row_2153, lowerTwo_row_2154, lowerTwo_row_2155, lowerTwo_row_2156, lowerTwo_row_2157, lowerTwo_row_2158, lowerTwo_row_2159, lowerTwo_row_2160, lowerTwo_row_2161, lowerTwo_row_2162, lowerTwo_row_2163, lowerTwo_row_2164, lowerTwo_row_2165, lowerTwo_row_2166, lowerTwo_row_2167, lowerTwo_row_2168, lowerTwo_row_2169, lowerTwo_row_2170, lowerTwo_row_2171, lowerTwo_row_2172, lowerTwo_row_2173, lowerTwo_row_2174, lowerTwo_row_2175, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
