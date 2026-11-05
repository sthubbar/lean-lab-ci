/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_58
import LeanLab.BHP1997.Certificate312Support

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_3776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3776 j) = 125336205 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3777 j) = 125048844 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3778 j) = 125064902 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3779 j) = 124777434 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3780 j) = 124793474 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3781 j) = 124505897 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3782 j) = 124521943 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3783 j) = 124234268 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3784 j) = 124250297 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3785 j) = 123962544 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3786 j) = 123978548 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3787 j) = 123690698 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3788 j) = 123706703 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3789 j) = 123418747 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3790 j) = 123434764 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3791 j) = 123146695 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3792 j) = 123162697 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3793 j) = 122874538 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3794 j) = 122890521 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3795 j) = 122602256 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3796 j) = 122618250 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3797 j) = 122329871 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3798 j) = 122345857 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3799 j) = 122057386 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3800 j) = 122073359 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3801 j) = 121784801 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3802 j) = 121800760 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3803 j) = 121512093 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3804 j) = 121528052 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3805 j) = 121239284 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3806 j) = 121255227 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3807 j) = 120966351 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3808 j) = 120982303 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3809 j) = 120693314 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3810 j) = 120709258 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3811 j) = 120420176 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3812 j) = 120436099 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3813 j) = 120146927 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3814 j) = 120162835 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3815 j) = 119873558 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3816 j) = 120200718 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3817 j) = 121156859 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3818 j) = 122419060 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3819 j) = 123376654 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3820 j) = 124640398 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3821 j) = 125599444 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3822 j) = 126864738 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3823 j) = 127825270 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3824 j) = 129092155 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3825 j) = 130054172 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3826 j) = 131322663 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3827 j) = 132286186 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3828 j) = 133556286 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3829 j) = 134521357 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3830 j) = 135793100 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3831 j) = 136759703 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3832 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3832 j) = 138033103 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3833 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3833 j) = 139001291 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3834 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3834 j) = 140276360 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3835 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3835 j) = 141246128 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3836 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3836 j) = 142522909 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3837 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3837 j) = 143494292 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3838 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3838 j) = 144772770 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel
private theorem lowerTwo_row_3839 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 3839 j) = 145745788 := by
  rewrite [lowerTwo_row_support_sum]
  decide +kernel

/-- Page 51. Exact E2 row block 3776 through 3839. -/
theorem lowerTwo_rows312_59 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (3776+i) j) = 8094899140 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_3776, lowerTwo_row_3777, lowerTwo_row_3778, lowerTwo_row_3779, lowerTwo_row_3780, lowerTwo_row_3781, lowerTwo_row_3782, lowerTwo_row_3783, lowerTwo_row_3784, lowerTwo_row_3785, lowerTwo_row_3786, lowerTwo_row_3787, lowerTwo_row_3788, lowerTwo_row_3789, lowerTwo_row_3790, lowerTwo_row_3791, lowerTwo_row_3792, lowerTwo_row_3793, lowerTwo_row_3794, lowerTwo_row_3795, lowerTwo_row_3796, lowerTwo_row_3797, lowerTwo_row_3798, lowerTwo_row_3799, lowerTwo_row_3800, lowerTwo_row_3801, lowerTwo_row_3802, lowerTwo_row_3803, lowerTwo_row_3804, lowerTwo_row_3805, lowerTwo_row_3806, lowerTwo_row_3807, lowerTwo_row_3808, lowerTwo_row_3809, lowerTwo_row_3810, lowerTwo_row_3811, lowerTwo_row_3812, lowerTwo_row_3813, lowerTwo_row_3814, lowerTwo_row_3815, lowerTwo_row_3816, lowerTwo_row_3817, lowerTwo_row_3818, lowerTwo_row_3819, lowerTwo_row_3820, lowerTwo_row_3821, lowerTwo_row_3822, lowerTwo_row_3823, lowerTwo_row_3824, lowerTwo_row_3825, lowerTwo_row_3826, lowerTwo_row_3827, lowerTwo_row_3828, lowerTwo_row_3829, lowerTwo_row_3830, lowerTwo_row_3831, lowerTwo_row_3832, lowerTwo_row_3833, lowerTwo_row_3834, lowerTwo_row_3835, lowerTwo_row_3836, lowerTwo_row_3837, lowerTwo_row_3838, lowerTwo_row_3839, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
