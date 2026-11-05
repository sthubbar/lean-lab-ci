/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_29
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_1920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1920 j) = 494209608 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1921 j) = 492691658 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1922 j) = 493126140 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1923 j) = 493560853 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1924 j) = 492594420 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1925 j) = 493028182 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1926 j) = 491811664 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1927 j) = 491933933 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1928 j) = 491272511 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1929 j) = 491704167 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1930 j) = 491824434 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1931 j) = 490601464 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1932 j) = 491031978 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1933 j) = 490052806 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1934 j) = 490482323 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1935 j) = 489814243 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1936 j) = 489368629 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1937 j) = 489796980 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1938 j) = 489125687 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1939 j) = 489237675 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1940 j) = 488564455 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1941 j) = 488429591 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1942 j) = 487437442 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1943 j) = 487862643 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1944 j) = 488288147 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1945 j) = 487291928 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1946 j) = 487153511 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1947 j) = 486473214 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1948 j) = 486577165 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1949 j) = 485894974 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1950 j) = 486317331 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1951 j) = 485854943 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1952 j) = 485169498 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1953 j) = 485590693 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1954 j) = 484581651 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1955 j) = 485001857 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1956 j) = 483747114 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1957 j) = 483842897 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1958 j) = 484261966 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1959 j) = 483569630 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1960 j) = 483663359 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1961 j) = 482401927 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1962 j) = 482818752 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1963 j) = 481796642 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1964 j) = 482212428 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1965 j) = 482628434 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1966 j) = 481033450 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1967 j) = 481448014 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1968 j) = 480746306 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1969 j) = 480831752 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1970 j) = 480128078 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1971 j) = 479970723 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1972 j) = 480053597 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1973 j) = 479346517 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1974 j) = 479757980 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1975 j) = 478718212 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1976 j) = 478557042 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1977 j) = 477845836 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1978 j) = 477922730 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1979 j) = 478331808 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1980 j) = 477617552 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1981 j) = 477119218 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1982 j) = 476402499 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_1983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1983 j) = 476809280 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 1920 through 1983. -/
theorem lowerTwo_rows312_30 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (1920+i) j) = 31067342141 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_1920, lowerTwo_row_1921, lowerTwo_row_1922, lowerTwo_row_1923, lowerTwo_row_1924, lowerTwo_row_1925, lowerTwo_row_1926, lowerTwo_row_1927, lowerTwo_row_1928, lowerTwo_row_1929, lowerTwo_row_1930, lowerTwo_row_1931, lowerTwo_row_1932, lowerTwo_row_1933, lowerTwo_row_1934, lowerTwo_row_1935, lowerTwo_row_1936, lowerTwo_row_1937, lowerTwo_row_1938, lowerTwo_row_1939, lowerTwo_row_1940, lowerTwo_row_1941, lowerTwo_row_1942, lowerTwo_row_1943, lowerTwo_row_1944, lowerTwo_row_1945, lowerTwo_row_1946, lowerTwo_row_1947, lowerTwo_row_1948, lowerTwo_row_1949, lowerTwo_row_1950, lowerTwo_row_1951, lowerTwo_row_1952, lowerTwo_row_1953, lowerTwo_row_1954, lowerTwo_row_1955, lowerTwo_row_1956, lowerTwo_row_1957, lowerTwo_row_1958, lowerTwo_row_1959, lowerTwo_row_1960, lowerTwo_row_1961, lowerTwo_row_1962, lowerTwo_row_1963, lowerTwo_row_1964, lowerTwo_row_1965, lowerTwo_row_1966, lowerTwo_row_1967, lowerTwo_row_1968, lowerTwo_row_1969, lowerTwo_row_1970, lowerTwo_row_1971, lowerTwo_row_1972, lowerTwo_row_1973, lowerTwo_row_1974, lowerTwo_row_1975, lowerTwo_row_1976, lowerTwo_row_1977, lowerTwo_row_1978, lowerTwo_row_1979, lowerTwo_row_1980, lowerTwo_row_1981, lowerTwo_row_1982, lowerTwo_row_1983, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
