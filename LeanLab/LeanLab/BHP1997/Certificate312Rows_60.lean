/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/

import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3840 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3840 j) = 147026014 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3841 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3841 j) = 148000672 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3842 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3842 j) = 149282632 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3843 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3843 j) = 150258971 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3844 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3844 j) = 151542715 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3845 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3845 j) = 152520733 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3846 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3846 j) = 153806276 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3847 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3847 j) = 154785994 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3848 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3848 j) = 156073364 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3849 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3849 j) = 157054818 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3850 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3850 j) = 158344021 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3851 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3851 j) = 159327210 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3852 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3852 j) = 160618265 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3853 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3853 j) = 161603218 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3854 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3854 j) = 162896162 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3855 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3855 j) = 163882913 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3856 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3856 j) = 165177777 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3857 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3857 j) = 166166309 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3858 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3858 j) = 167463068 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3859 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3859 j) = 168453480 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3860 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3860 j) = 169752162 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3861 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3861 j) = 170744426 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3862 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3862 j) = 172045071 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3863 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3863 j) = 173039203 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3864 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3864 j) = 174341837 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3865 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3865 j) = 175337877 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3866 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3866 j) = 176642516 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3867 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3867 j) = 177640473 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3868 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3868 j) = 178947137 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3869 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3869 j) = 179947027 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3870 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3870 j) = 181255747 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3871 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3871 j) = 182257618 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3872 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3872 j) = 183568398 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3873 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3873 j) = 184572257 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3874 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3874 j) = 185885135 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3875 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3875 j) = 186890976 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3876 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3876 j) = 188206003 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3877 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3877 j) = 189213864 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3878 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3878 j) = 190531032 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3879 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3879 j) = 191540944 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3880 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3880 j) = 192860263 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3881 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3881 j) = 193872303 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3882 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3882 j) = 195193797 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3883 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3883 j) = 196207895 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3884 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3884 j) = 197531621 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3885 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3885 j) = 198547866 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3886 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3886 j) = 199873820 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3887 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3887 j) = 200892193 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3888 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3888 j) = 202220416 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3889 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3889 j) = 203240963 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3890 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3890 j) = 204571467 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3891 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3891 j) = 205594233 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3892 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3892 j) = 206927034 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3893 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3893 j) = 207951997 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3894 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3894 j) = 209287156 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3895 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3895 j) = 210314379 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3896 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3896 j) = 211651879 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3897 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3897 j) = 212681370 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3898 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3898 j) = 214021253 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3899 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3899 j) = 215053054 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3900 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3900 j) = 216395340 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3901 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3901 j) = 217429453 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3902 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3902 j) = 218774180 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3903 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3903 j) = 219810656 := by
  rw [lowerTwo_row_support_sum]
  decide +kernel
/-- Page 51. Exact E2 row block 3840 through 3903. -/
theorem lowerTwo_rows312_60 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3840+i) j) = 11717548903 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3840, lowerTwo_row_3841, lowerTwo_row_3842, lowerTwo_row_3843, lowerTwo_row_3844, lowerTwo_row_3845, lowerTwo_row_3846, lowerTwo_row_3847, lowerTwo_row_3848, lowerTwo_row_3849, lowerTwo_row_3850, lowerTwo_row_3851, lowerTwo_row_3852, lowerTwo_row_3853, lowerTwo_row_3854, lowerTwo_row_3855, lowerTwo_row_3856, lowerTwo_row_3857, lowerTwo_row_3858, lowerTwo_row_3859, lowerTwo_row_3860, lowerTwo_row_3861, lowerTwo_row_3862, lowerTwo_row_3863, lowerTwo_row_3864, lowerTwo_row_3865, lowerTwo_row_3866, lowerTwo_row_3867, lowerTwo_row_3868, lowerTwo_row_3869, lowerTwo_row_3870, lowerTwo_row_3871, lowerTwo_row_3872, lowerTwo_row_3873, lowerTwo_row_3874, lowerTwo_row_3875, lowerTwo_row_3876, lowerTwo_row_3877, lowerTwo_row_3878, lowerTwo_row_3879, lowerTwo_row_3880, lowerTwo_row_3881, lowerTwo_row_3882, lowerTwo_row_3883, lowerTwo_row_3884, lowerTwo_row_3885, lowerTwo_row_3886, lowerTwo_row_3887, lowerTwo_row_3888, lowerTwo_row_3889, lowerTwo_row_3890, lowerTwo_row_3891, lowerTwo_row_3892, lowerTwo_row_3893, lowerTwo_row_3894, lowerTwo_row_3895, lowerTwo_row_3896, lowerTwo_row_3897, lowerTwo_row_3898, lowerTwo_row_3899, lowerTwo_row_3900, lowerTwo_row_3901, lowerTwo_row_3902, lowerTwo_row_3903, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
