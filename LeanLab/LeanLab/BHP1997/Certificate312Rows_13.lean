/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 832 j) = 104028362 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 833 j) = 105469760 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 834 j) = 106115974 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 835 j) = 107554626 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 836 j) = 108198046 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 837 j) = 109633967 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 838 j) = 111068716 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 839 j) = 111707783 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 840 j) = 113139830 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 841 j) = 113776118 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 842 j) = 115205463 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 843 j) = 115838998 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 844 j) = 117265638 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 845 j) = 118691138 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 846 j) = 119320385 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 847 j) = 120743218 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 848 j) = 121369739 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 849 j) = 122789895 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 850 j) = 123413705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 851 j) = 124831209 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 852 j) = 126247601 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 853 j) = 126867176 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 854 j) = 128280932 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 855 j) = 128897812 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 856 j) = 130308950 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 857 j) = 130923145 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 858 j) = 132331662 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 859 j) = 133739085 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 860 j) = 134349114 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 861 j) = 135753945 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 862 j) = 136361306 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 863 j) = 137763555 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 864 j) = 138368288 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 865 j) = 139767966 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 866 j) = 141166569 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 867 j) = 141767165 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 868 j) = 143163223 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 869 j) = 143761202 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 870 j) = 145154704 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 871 j) = 145750082 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 872 j) = 147141056 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 873 j) = 148530981 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 874 j) = 149122281 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 875 j) = 150509701 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 876 j) = 151098411 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 877 j) = 152483325 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 878 j) = 153069465 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 879 j) = 154451885 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 880 j) = 155833267 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 881 j) = 156415396 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 882 j) = 157794303 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 883 j) = 158373885 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 884 j) = 159750320 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 885 j) = 160327374 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 886 j) = 161701358 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 887 j) = 163074337 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 888 j) = 163647420 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 889 j) = 165017959 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 890 j) = 165588531 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 891 j) = 166956646 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 892 j) = 167524705 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 893 j) = 168890403 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 894 j) = 170255121 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 895 j) = 170819265 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 832 through 895. -/
theorem lowerTwo_rows312_13 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (832+i) j) = 8829263447 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_832, lowerTwo_row_833, lowerTwo_row_834, lowerTwo_row_835, lowerTwo_row_836, lowerTwo_row_837, lowerTwo_row_838, lowerTwo_row_839, lowerTwo_row_840, lowerTwo_row_841, lowerTwo_row_842, lowerTwo_row_843, lowerTwo_row_844, lowerTwo_row_845, lowerTwo_row_846, lowerTwo_row_847, lowerTwo_row_848, lowerTwo_row_849, lowerTwo_row_850, lowerTwo_row_851, lowerTwo_row_852, lowerTwo_row_853, lowerTwo_row_854, lowerTwo_row_855, lowerTwo_row_856, lowerTwo_row_857, lowerTwo_row_858, lowerTwo_row_859, lowerTwo_row_860, lowerTwo_row_861, lowerTwo_row_862, lowerTwo_row_863, lowerTwo_row_864, lowerTwo_row_865, lowerTwo_row_866, lowerTwo_row_867, lowerTwo_row_868, lowerTwo_row_869, lowerTwo_row_870, lowerTwo_row_871, lowerTwo_row_872, lowerTwo_row_873, lowerTwo_row_874, lowerTwo_row_875, lowerTwo_row_876, lowerTwo_row_877, lowerTwo_row_878, lowerTwo_row_879, lowerTwo_row_880, lowerTwo_row_881, lowerTwo_row_882, lowerTwo_row_883, lowerTwo_row_884, lowerTwo_row_885, lowerTwo_row_886, lowerTwo_row_887, lowerTwo_row_888, lowerTwo_row_889, lowerTwo_row_890, lowerTwo_row_891, lowerTwo_row_892, lowerTwo_row_893, lowerTwo_row_894, lowerTwo_row_895, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
