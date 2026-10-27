/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 11 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail10

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_8 : wem 76118712 76119912 78119910 &&& gm (wpm 76118712 2001198) (P10k.take 183) =
    wem 76118712 76119912 78119910 := by
  decide +kernel

theorem seg_28_8 : SmallGBUpTo 1093 78119910 :=
  small_extend_w (a := 76119910) (A := 76119912) (lo := 76118712) (W := 2001198) seg_28_7
    ⟨38059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_8

theorem window_28_9 : wem 78118712 78119912 80119910 &&& gm (wpm 78118712 2001198) (P10k.take 183) =
    wem 78118712 78119912 80119910 := by
  decide +kernel

theorem seg_28_9 : SmallGBUpTo 1093 80119910 :=
  small_extend_w (a := 78119910) (A := 78119912) (lo := 78118712) (W := 2001198) seg_28_8
    ⟨39059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_9


end LeanLab.OeSHP2014.Exact1e8
