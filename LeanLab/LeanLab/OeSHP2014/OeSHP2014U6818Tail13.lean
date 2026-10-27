/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 13 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail12

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_12 : wem 84118712 84119912 86119910 &&& gm (wpm 84118712 2001198) (P10k.take 183) =
    wem 84118712 84119912 86119910 := by
  decide +kernel

theorem seg_28_12 : SmallGBUpTo 1093 86119910 :=
  small_extend_w (a := 84119910) (A := 84119912) (lo := 84118712) (W := 2001198) seg_28_11
    ⟨42059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_12

theorem window_28_13 : wem 86118712 86119912 88119910 &&& gm (wpm 86118712 2001198) (P10k.take 183) =
    wem 86118712 86119912 88119910 := by
  decide +kernel

theorem seg_28_13 : SmallGBUpTo 1093 88119910 :=
  small_extend_w (a := 86119910) (A := 86119912) (lo := 86118712) (W := 2001198) seg_28_12
    ⟨43059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_13


end LeanLab.OeSHP2014.Exact1e8
