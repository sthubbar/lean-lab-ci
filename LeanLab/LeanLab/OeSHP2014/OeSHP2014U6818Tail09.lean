/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 9 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail08

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_4 : wem 68118712 68119912 70119910 &&& gm (wpm 68118712 2001198) (P10k.take 183) =
    wem 68118712 68119912 70119910 := by
  decide +kernel

theorem seg_28_4 : SmallGBUpTo 1093 70119910 :=
  small_extend_w (a := 68119910) (A := 68119912) (lo := 68118712) (W := 2001198) seg_28_3
    ⟨34059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_4

theorem window_28_5 : wem 70118712 70119912 72119910 &&& gm (wpm 70118712 2001198) (P10k.take 183) =
    wem 70118712 70119912 72119910 := by
  decide +kernel

theorem seg_28_5 : SmallGBUpTo 1093 72119910 :=
  small_extend_w (a := 70119910) (A := 70119912) (lo := 70118712) (W := 2001198) seg_28_4
    ⟨35059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_5


end LeanLab.OeSHP2014.Exact1e8
