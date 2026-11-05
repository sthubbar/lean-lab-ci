/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_13

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 896 j) = 172181573 := by decide
private theorem lowerTwo_row_897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 897 j) = 172743244 := by decide
private theorem lowerTwo_row_898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 898 j) = 174103162 := by decide
private theorem lowerTwo_row_899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 899 j) = 174662358 := by decide
private theorem lowerTwo_row_900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 900 j) = 176019897 := by decide
private theorem lowerTwo_row_901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 901 j) = 177376469 := by decide
private theorem lowerTwo_row_902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 902 j) = 177931808 := by decide
private theorem lowerTwo_row_903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 903 j) = 179286020 := by decide
private theorem lowerTwo_row_904 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 904 j) = 179838915 := by decide
private theorem lowerTwo_row_905 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 905 j) = 181190767 := by decide
private theorem lowerTwo_row_906 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 906 j) = 181741220 := by decide
private theorem lowerTwo_row_907 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 907 j) = 183090737 := by decide
private theorem lowerTwo_row_908 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 908 j) = 184439285 := by decide
private theorem lowerTwo_row_909 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 909 j) = 184985937 := by decide
private theorem lowerTwo_row_910 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 910 j) = 186332174 := by decide
private theorem lowerTwo_row_911 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 911 j) = 186876414 := by decide
private theorem lowerTwo_row_912 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 912 j) = 188220330 := by decide
private theorem lowerTwo_row_913 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 913 j) = 188762156 := by decide
private theorem lowerTwo_row_914 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 914 j) = 190103762 := by decide
private theorem lowerTwo_row_915 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 915 j) = 191444460 := by decide
private theorem lowerTwo_row_916 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 916 j) = 191982519 := by decide
private theorem lowerTwo_row_917 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 917 j) = 193320915 := by decide
private theorem lowerTwo_row_918 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 918 j) = 193856591 := by decide
private theorem lowerTwo_row_919 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 919 j) = 195192714 := by decide
private theorem lowerTwo_row_920 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 920 j) = 195726025 := by decide
private theorem lowerTwo_row_921 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 921 j) = 197059866 := by decide
private theorem lowerTwo_row_922 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 922 j) = 198392799 := by decide
private theorem lowerTwo_row_923 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 923 j) = 198922387 := by decide
private theorem lowerTwo_row_924 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 924 j) = 200253071 := by decide
private theorem lowerTwo_row_925 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 925 j) = 200780319 := by decide
private theorem lowerTwo_row_926 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 926 j) = 202108748 := by decide
private theorem lowerTwo_row_927 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 927 j) = 202633658 := by decide
private theorem lowerTwo_row_928 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 928 j) = 203959852 := by decide
private theorem lowerTwo_row_929 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 929 j) = 205285157 := by decide
private theorem lowerTwo_row_930 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 930 j) = 205806410 := by decide
private theorem lowerTwo_row_931 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 931 j) = 207129486 := by decide
private theorem lowerTwo_row_932 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 932 j) = 207648401 := by decide
private theorem lowerTwo_row_933 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 933 j) = 208969276 := by decide
private theorem lowerTwo_row_934 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 934 j) = 209485891 := by decide
private theorem lowerTwo_row_935 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 935 j) = 210804576 := by decide
private theorem lowerTwo_row_936 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 936 j) = 212122380 := by decide
private theorem lowerTwo_row_937 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 937 j) = 212635362 := by decide
private theorem lowerTwo_row_938 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 938 j) = 213950986 := by decide
private theorem lowerTwo_row_939 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 939 j) = 214461673 := by decide
private theorem lowerTwo_row_940 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 940 j) = 215775117 := by decide
private theorem lowerTwo_row_941 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 941 j) = 216283553 := by decide
private theorem lowerTwo_row_942 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 942 j) = 217594831 := by decide
private theorem lowerTwo_row_943 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 943 j) = 218905258 := by decide
private theorem lowerTwo_row_944 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 944 j) = 219410097 := by decide
private theorem lowerTwo_row_945 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 945 j) = 220718364 := by decide
private theorem lowerTwo_row_946 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 946 j) = 221220963 := by decide
private theorem lowerTwo_row_947 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 947 j) = 222527098 := by decide
private theorem lowerTwo_row_948 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 948 j) = 223027423 := by decide
private theorem lowerTwo_row_949 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 949 j) = 224331436 := by decide
private theorem lowerTwo_row_950 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 950 j) = 225634594 := by decide
private theorem lowerTwo_row_951 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 951 j) = 226131400 := by decide
private theorem lowerTwo_row_952 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 952 j) = 227432455 := by decide
private theorem lowerTwo_row_953 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 953 j) = 227927035 := by decide
private theorem lowerTwo_row_954 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 954 j) = 229225977 := by decide
private theorem lowerTwo_row_955 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 955 j) = 229718333 := by decide
private theorem lowerTwo_row_956 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 956 j) = 231015188 := by decide
private theorem lowerTwo_row_957 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 957 j) = 232311200 := by decide
private theorem lowerTwo_row_958 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 958 j) = 232800082 := by decide
private theorem lowerTwo_row_959 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 959 j) = 234094012 := by decide

/-- Page 51. Exact E2 row block 896 through 959. -/
theorem lowerTwo_rows312_14 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (896+i) j) = 13009904166 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_896, lowerTwo_row_897, lowerTwo_row_898, lowerTwo_row_899, lowerTwo_row_900, lowerTwo_row_901, lowerTwo_row_902, lowerTwo_row_903, lowerTwo_row_904, lowerTwo_row_905, lowerTwo_row_906, lowerTwo_row_907, lowerTwo_row_908, lowerTwo_row_909, lowerTwo_row_910, lowerTwo_row_911, lowerTwo_row_912, lowerTwo_row_913, lowerTwo_row_914, lowerTwo_row_915, lowerTwo_row_916, lowerTwo_row_917, lowerTwo_row_918, lowerTwo_row_919, lowerTwo_row_920, lowerTwo_row_921, lowerTwo_row_922, lowerTwo_row_923, lowerTwo_row_924, lowerTwo_row_925, lowerTwo_row_926, lowerTwo_row_927, lowerTwo_row_928, lowerTwo_row_929, lowerTwo_row_930, lowerTwo_row_931, lowerTwo_row_932, lowerTwo_row_933, lowerTwo_row_934, lowerTwo_row_935, lowerTwo_row_936, lowerTwo_row_937, lowerTwo_row_938, lowerTwo_row_939, lowerTwo_row_940, lowerTwo_row_941, lowerTwo_row_942, lowerTwo_row_943, lowerTwo_row_944, lowerTwo_row_945, lowerTwo_row_946, lowerTwo_row_947, lowerTwo_row_948, lowerTwo_row_949, lowerTwo_row_950, lowerTwo_row_951, lowerTwo_row_952, lowerTwo_row_953, lowerTwo_row_954, lowerTwo_row_955, lowerTwo_row_956, lowerTwo_row_957, lowerTwo_row_958, lowerTwo_row_959, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
