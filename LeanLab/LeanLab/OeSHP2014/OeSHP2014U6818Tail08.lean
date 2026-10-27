/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 8 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail07

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_2 : wem 64118712 64119912 66119910 &&& gm (wpm 64118712 2001198) (P10k.take 183) =
    wem 64118712 64119912 66119910 := by
  decide +kernel

theorem seg_28_2 : SmallGBUpTo 1093 66119910 :=
  small_extend_w (a := 64119910) (A := 64119912) (lo := 64118712) (W := 2001198) seg_28_1
    ⟨32059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_2

theorem window_28_3 : wem 66118712 66119912 68119910 &&& gm (wpm 66118712 2001198) (P10k.take 183) =
    wem 66118712 66119912 68119910 := by
  decide +kernel

theorem seg_28_3 : SmallGBUpTo 1093 68119910 :=
  small_extend_w (a := 66119910) (A := 66119912) (lo := 66118712) (W := 2001198) seg_28_2
    ⟨33059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_3


end LeanLab.OeSHP2014.Exact1e8
