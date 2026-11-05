/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_14

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_960 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 960 j) = 234580691 := by decide
private theorem lowerTwo_row_961 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 961 j) = 235872549 := by decide
private theorem lowerTwo_row_962 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 962 j) = 236357039 := by decide
private theorem lowerTwo_row_963 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 963 j) = 237646837 := by decide
private theorem lowerTwo_row_964 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 964 j) = 238935834 := by decide
private theorem lowerTwo_row_965 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 965 j) = 239416874 := by decide
private theorem lowerTwo_row_966 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 966 j) = 240703819 := by decide
private theorem lowerTwo_row_967 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 967 j) = 241182685 := by decide
private theorem lowerTwo_row_968 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 968 j) = 242467606 := by decide
private theorem lowerTwo_row_969 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 969 j) = 242944281 := by decide
private theorem lowerTwo_row_970 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 970 j) = 244227071 := by decide
private theorem lowerTwo_row_971 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 971 j) = 245509018 := by decide
private theorem lowerTwo_row_972 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 972 j) = 245982134 := by decide
private theorem lowerTwo_row_973 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 973 j) = 247261961 := by decide
private theorem lowerTwo_row_974 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 974 j) = 247732800 := by decide
private theorem lowerTwo_row_975 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 975 j) = 249010506 := by decide
private theorem lowerTwo_row_976 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 976 j) = 249479108 := by decide
private theorem lowerTwo_row_977 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 977 j) = 250754688 := by decide
private theorem lowerTwo_row_978 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 978 j) = 252029442 := by decide
private theorem lowerTwo_row_979 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 979 j) = 252494552 := by decide
private theorem lowerTwo_row_980 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 980 j) = 253767206 := by decide
private theorem lowerTwo_row_981 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 981 j) = 254230075 := by decide
private theorem lowerTwo_row_982 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 982 j) = 255500642 := by decide
private theorem lowerTwo_row_983 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 983 j) = 255961292 := by decide
private theorem lowerTwo_row_984 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 984 j) = 257229800 := by decide
private theorem lowerTwo_row_985 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 985 j) = 258497496 := by decide
private theorem lowerTwo_row_986 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 986 j) = 258954652 := by decide
private theorem lowerTwo_row_987 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 987 j) = 260220292 := by decide
private theorem lowerTwo_row_988 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 988 j) = 260675265 := by decide
private theorem lowerTwo_row_989 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 989 j) = 261938846 := by decide
private theorem lowerTwo_row_990 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 990 j) = 262391620 := by decide
private theorem lowerTwo_row_991 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 991 j) = 263653144 := by decide
private theorem lowerTwo_row_992 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 992 j) = 264913900 := by decide
private theorem lowerTwo_row_993 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 993 j) = 265363242 := by decide
private theorem lowerTwo_row_994 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 994 j) = 266621953 := by decide
private theorem lowerTwo_row_995 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 995 j) = 267069137 := by decide
private theorem lowerTwo_row_996 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 996 j) = 268325825 := by decide
private theorem lowerTwo_row_997 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 997 j) = 268770839 := by decide
private theorem lowerTwo_row_998 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 998 j) = 270025508 := by decide
private theorem lowerTwo_row_999 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 999 j) = 271279421 := by decide
private theorem lowerTwo_row_1000 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1000 j) = 271721052 := by decide
private theorem lowerTwo_row_1001 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1001 j) = 272972961 := by decide
private theorem lowerTwo_row_1002 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1002 j) = 273412449 := by decide
private theorem lowerTwo_row_1003 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1003 j) = 274662363 := by decide
private theorem lowerTwo_row_1004 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1004 j) = 275099717 := by decide
private theorem lowerTwo_row_1005 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1005 j) = 276347640 := by decide
private theorem lowerTwo_row_1006 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1006 j) = 277594839 := by decide
private theorem lowerTwo_row_1007 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1007 j) = 278028836 := by decide
private theorem lowerTwo_row_1008 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1008 j) = 279274044 := by decide
private theorem lowerTwo_row_1009 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1009 j) = 279705937 := by decide
private theorem lowerTwo_row_1010 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1010 j) = 280949199 := by decide
private theorem lowerTwo_row_1011 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1011 j) = 281378994 := by decide
private theorem lowerTwo_row_1012 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1012 j) = 282620285 := by decide
private theorem lowerTwo_row_1013 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1013 j) = 283860850 := by decide
private theorem lowerTwo_row_1014 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1014 j) = 284287340 := by decide
private theorem lowerTwo_row_1015 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1015 j) = 285525960 := by decide
private theorem lowerTwo_row_1016 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1016 j) = 285950361 := by decide
private theorem lowerTwo_row_1017 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1017 j) = 287187068 := by decide
private theorem lowerTwo_row_1018 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1018 j) = 287609377 := by decide
private theorem lowerTwo_row_1019 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1019 j) = 288844153 := by decide
private theorem lowerTwo_row_1020 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1020 j) = 290078210 := by decide
private theorem lowerTwo_row_1021 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1021 j) = 290497263 := by decide
private theorem lowerTwo_row_1022 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1022 j) = 291729418 := by decide
private theorem lowerTwo_row_1023 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 1023 j) = 292146420 := by decide

/-- Page 51. Exact E2 row block 960 through 1023. -/
theorem lowerTwo_rows312_15 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (960+i) j) = 16891464386 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_960, lowerTwo_row_961, lowerTwo_row_962, lowerTwo_row_963, lowerTwo_row_964, lowerTwo_row_965, lowerTwo_row_966, lowerTwo_row_967, lowerTwo_row_968, lowerTwo_row_969, lowerTwo_row_970, lowerTwo_row_971, lowerTwo_row_972, lowerTwo_row_973, lowerTwo_row_974, lowerTwo_row_975, lowerTwo_row_976, lowerTwo_row_977, lowerTwo_row_978, lowerTwo_row_979, lowerTwo_row_980, lowerTwo_row_981, lowerTwo_row_982, lowerTwo_row_983, lowerTwo_row_984, lowerTwo_row_985, lowerTwo_row_986, lowerTwo_row_987, lowerTwo_row_988, lowerTwo_row_989, lowerTwo_row_990, lowerTwo_row_991, lowerTwo_row_992, lowerTwo_row_993, lowerTwo_row_994, lowerTwo_row_995, lowerTwo_row_996, lowerTwo_row_997, lowerTwo_row_998, lowerTwo_row_999, lowerTwo_row_1000, lowerTwo_row_1001, lowerTwo_row_1002, lowerTwo_row_1003, lowerTwo_row_1004, lowerTwo_row_1005, lowerTwo_row_1006, lowerTwo_row_1007, lowerTwo_row_1008, lowerTwo_row_1009, lowerTwo_row_1010, lowerTwo_row_1011, lowerTwo_row_1012, lowerTwo_row_1013, lowerTwo_row_1014, lowerTwo_row_1015, lowerTwo_row_1016, lowerTwo_row_1017, lowerTwo_row_1018, lowerTwo_row_1019, lowerTwo_row_1020, lowerTwo_row_1021, lowerTwo_row_1022, lowerTwo_row_1023, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
