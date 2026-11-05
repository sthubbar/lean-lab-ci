/-
P0069, page 51. Bounded E2 grid certificate shard.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Certificate312Rows_11

namespace LeanLab.BHP1997.DecompC165d
open Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem lowerTwo_row_768 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 768 j) = 30990042 := by decide
private theorem lowerTwo_row_769 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 769 j) = 31735043 := by decide
private theorem lowerTwo_row_770 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 770 j) = 33267820 := by decide
private theorem lowerTwo_row_771 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 771 j) = 34009641 := by decide
private theorem lowerTwo_row_772 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 772 j) = 35539249 := by decide
private theorem lowerTwo_row_773 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 773 j) = 36277896 := by decide
private theorem lowerTwo_row_774 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 774 j) = 37804363 := by decide
private theorem lowerTwo_row_775 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 775 j) = 39329452 := by decide
private theorem lowerTwo_row_776 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 776 j) = 40063185 := by decide
private theorem lowerTwo_row_777 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 777 j) = 41585145 := by decide
private theorem lowerTwo_row_778 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 778 j) = 42315735 := by decide
private theorem lowerTwo_row_779 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 779 j) = 43834586 := by decide
private theorem lowerTwo_row_780 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 780 j) = 44562056 := by decide
private theorem lowerTwo_row_781 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 781 j) = 46077809 := by decide
private theorem lowerTwo_row_782 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 782 j) = 47592205 := by decide
private theorem lowerTwo_row_783 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 783 j) = 48314820 := by decide
private theorem lowerTwo_row_784 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 784 j) = 49826147 := by decide
private theorem lowerTwo_row_785 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 785 j) = 50545666 := by decide
private theorem lowerTwo_row_786 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 786 j) = 52053930 := by decide
private theorem lowerTwo_row_787 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 787 j) = 52770358 := by decide
private theorem lowerTwo_row_788 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 788 j) = 54275573 := by decide
private theorem lowerTwo_row_789 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 789 j) = 55779448 := by decide
private theorem lowerTwo_row_790 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 790 j) = 56491111 := by decide
private theorem lowerTwo_row_791 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 791 j) = 57991961 := by decide
private theorem lowerTwo_row_792 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 792 j) = 58700568 := by decide
private theorem lowerTwo_row_793 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 793 j) = 60198394 := by decide
private theorem lowerTwo_row_794 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 794 j) = 60903971 := by decide
private theorem lowerTwo_row_795 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 795 j) = 62398798 := by decide
private theorem lowerTwo_row_796 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 796 j) = 63892321 := by decide
private theorem lowerTwo_row_797 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 797 j) = 64593176 := by decide
private theorem lowerTwo_row_798 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 798 j) = 66083712 := by decide
private theorem lowerTwo_row_799 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 799 j) = 66781555 := by decide
private theorem lowerTwo_row_800 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 800 j) = 68269128 := by decide
private theorem lowerTwo_row_801 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 801 j) = 68963978 := by decide
private theorem lowerTwo_row_802 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 802 j) = 70448588 := by decide
private theorem lowerTwo_row_803 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 803 j) = 71931925 := by decide
private theorem lowerTwo_row_804 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 804 j) = 72622121 := by decide
private theorem lowerTwo_row_805 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 805 j) = 74102517 := by decide
private theorem lowerTwo_row_806 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 806 j) = 74789745 := by decide
private theorem lowerTwo_row_807 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 807 j) = 76267215 := by decide
private theorem lowerTwo_row_808 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 808 j) = 76951492 := by decide
private theorem lowerTwo_row_809 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 809 j) = 78426055 := by decide
private theorem lowerTwo_row_810 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 810 j) = 79899359 := by decide
private theorem lowerTwo_row_811 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 811 j) = 80579048 := by decide
private theorem lowerTwo_row_812 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 812 j) = 82049463 := by decide
private theorem lowerTwo_row_813 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 813 j) = 82726221 := by decide
private theorem lowerTwo_row_814 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 814 j) = 84193751 := by decide
private theorem lowerTwo_row_815 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 815 j) = 84867611 := by decide
private theorem lowerTwo_row_816 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 816 j) = 86332268 := by decide
private theorem lowerTwo_row_817 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 817 j) = 87795707 := by decide
private theorem lowerTwo_row_818 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 818 j) = 88465031 := by decide
private theorem lowerTwo_row_819 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 819 j) = 89925620 := by decide
private theorem lowerTwo_row_820 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 820 j) = 90592053 := by decide
private theorem lowerTwo_row_821 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 821 j) = 92049811 := by decide
private theorem lowerTwo_row_822 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 822 j) = 92713368 := by decide
private theorem lowerTwo_row_823 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 823 j) = 94168299 := by decide
private theorem lowerTwo_row_824 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 824 j) = 95622020 := by decide
private theorem lowerTwo_row_825 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 825 j) = 96281114 := by decide
private theorem lowerTwo_row_826 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 826 j) = 97732042 := by decide
private theorem lowerTwo_row_827 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 827 j) = 98388294 := by decide
private theorem lowerTwo_row_828 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 828 j) = 99836415 := by decide
private theorem lowerTwo_row_829 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 829 j) = 100489836 := by decide
private theorem lowerTwo_row_830 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 830 j) = 101935187 := by decide
private theorem lowerTwo_row_831 :
    (∑ j ∈ Finset.range 4096, lowerTwoGridWeight 831 j) = 103379352 := by decide

/-- Page 51. Exact E2 row block 768 through 831. -/
theorem lowerTwo_rows312_12 :
    (∑ i ∈ Finset.range 64, ∑ j ∈ Finset.range 4096, lowerTwoGridWeight (768+i) j) = 4309380370 := by
  simp only [lowerTwo_shifted_row_peel, Nat.reduceAdd, lowerTwo_row_768, lowerTwo_row_769, lowerTwo_row_770, lowerTwo_row_771, lowerTwo_row_772, lowerTwo_row_773, lowerTwo_row_774, lowerTwo_row_775, lowerTwo_row_776, lowerTwo_row_777, lowerTwo_row_778, lowerTwo_row_779, lowerTwo_row_780, lowerTwo_row_781, lowerTwo_row_782, lowerTwo_row_783, lowerTwo_row_784, lowerTwo_row_785, lowerTwo_row_786, lowerTwo_row_787, lowerTwo_row_788, lowerTwo_row_789, lowerTwo_row_790, lowerTwo_row_791, lowerTwo_row_792, lowerTwo_row_793, lowerTwo_row_794, lowerTwo_row_795, lowerTwo_row_796, lowerTwo_row_797, lowerTwo_row_798, lowerTwo_row_799, lowerTwo_row_800, lowerTwo_row_801, lowerTwo_row_802, lowerTwo_row_803, lowerTwo_row_804, lowerTwo_row_805, lowerTwo_row_806, lowerTwo_row_807, lowerTwo_row_808, lowerTwo_row_809, lowerTwo_row_810, lowerTwo_row_811, lowerTwo_row_812, lowerTwo_row_813, lowerTwo_row_814, lowerTwo_row_815, lowerTwo_row_816, lowerTwo_row_817, lowerTwo_row_818, lowerTwo_row_819, lowerTwo_row_820, lowerTwo_row_821, lowerTwo_row_822, lowerTwo_row_823, lowerTwo_row_824, lowerTwo_row_825, lowerTwo_row_826, lowerTwo_row_827, lowerTwo_row_828, lowerTwo_row_829, lowerTwo_row_830, lowerTwo_row_831, Finset.sum_range_zero]
  all_goals decide

end LeanLab.BHP1997.DecompC165d
