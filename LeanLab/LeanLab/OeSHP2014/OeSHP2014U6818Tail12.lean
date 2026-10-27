/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 12 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail11

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_10 : wem 80118712 80119912 82119910 &&& gm (wpm 80118712 2001198) (P10k.take 183) =
    wem 80118712 80119912 82119910 := by
  decide +kernel

theorem seg_28_10 : SmallGBUpTo 1093 82119910 :=
  small_extend_w (a := 80119910) (A := 80119912) (lo := 80118712) (W := 2001198) seg_28_9
    ⟨40059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_10

theorem window_28_11 : wem 82118712 82119912 84119910 &&& gm (wpm 82118712 2001198) (P10k.take 183) =
    wem 82118712 82119912 84119910 := by
  decide +kernel

theorem seg_28_11 : SmallGBUpTo 1093 84119910 :=
  small_extend_w (a := 82119910) (A := 82119912) (lo := 82118712) (W := 2001198) seg_28_10
    ⟨41059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_11


end LeanLab.OeSHP2014.Exact1e8
