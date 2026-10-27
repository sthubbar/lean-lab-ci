/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 15 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail14

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_16 : wem 92118712 92119912 94119910 &&& gm (wpm 92118712 2001198) (P10k.take 183) =
    wem 92118712 92119912 94119910 := by
  decide +kernel

theorem seg_28_16 : SmallGBUpTo 1093 94119910 :=
  small_extend_w (a := 92119910) (A := 92119912) (lo := 92118712) (W := 2001198) seg_28_15
    ⟨46059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_16

theorem window_28_17 : wem 94118712 94119912 96119910 &&& gm (wpm 94118712 2001198) (P10k.take 183) =
    wem 94118712 94119912 96119910 := by
  decide +kernel

theorem seg_28_17 : SmallGBUpTo 1093 96119910 :=
  small_extend_w (a := 94119910) (A := 94119912) (lo := 94118712) (W := 2001198) seg_28_16
    ⟨47059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_17


end LeanLab.OeSHP2014.Exact1e8
