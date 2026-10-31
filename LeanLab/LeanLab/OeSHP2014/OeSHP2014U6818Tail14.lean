/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 14 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail13

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_14 : wem 88118712 88119912 90119910 &&& gm (wpm 88118712 2001198) (P10k.take 183) =
    wem 88118712 88119912 90119910 := by
  decide +kernel

theorem seg_28_14 : SmallGBUpTo 1093 90119910 :=
  small_extend_w (a := 88119910) (A := 88119912) (lo := 88118712) (W := 2001198) seg_28_13
    ⟨44059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_14

theorem window_28_15 : wem 90118712 90119912 92119910 &&& gm (wpm 90118712 2001198) (P10k.take 183) =
    wem 90118712 90119912 92119910 := by
  decide +kernel

theorem seg_28_15 : SmallGBUpTo 1093 92119910 :=
  small_extend_w (a := 90119910) (A := 90119912) (lo := 90118712) (W := 2001198) seg_28_14
    ⟨45059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_15


end LeanLab.OeSHP2014.Exact1e8
