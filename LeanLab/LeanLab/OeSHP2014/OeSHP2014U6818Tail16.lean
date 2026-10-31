/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 16 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail15

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_18 : wem 96118712 96119912 98119910 &&& gm (wpm 96118712 2001198) (P10k.take 183) =
    wem 96118712 96119912 98119910 := by
  decide +kernel

theorem seg_28_18 : SmallGBUpTo 1093 98119910 :=
  small_extend_w (a := 96119910) (A := 96119912) (lo := 96118712) (W := 2001198) seg_28_17
    ⟨48059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_18

theorem window_28_19 : wem 98118712 98119912 100000000 &&& gm (wpm 98118712 1881288) (P10k.take 183) =
    wem 98118712 98119912 100000000 := by
  decide +kernel

theorem seg_28_19 : SmallGBUpTo 1093 100000000 :=
  small_extend_w (a := 98119910) (A := 98119912) (lo := 98118712) (W := 1881288) seg_28_18
    ⟨49059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_19

theorem seg_28 : SmallGBUpTo 1093 100000000 := seg_28_19


end LeanLab.OeSHP2014.Exact1e8
