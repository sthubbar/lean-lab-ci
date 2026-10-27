/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 7 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail06

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_0 : wem 60118712 60119912 62119910 &&& gm (wpm 60118712 2001198) (P10k.take 183) =
    wem 60118712 60119912 62119910 := by
  decide +kernel

theorem seg_28_0 : SmallGBUpTo 1093 62119910 :=
  small_extend_w (a := 60119910) (A := 60119912) (lo := 60118712) (W := 2001198) (small_bound_mono seg_27 (by norm_num))
    ⟨30059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_0

theorem window_28_1 : wem 62118712 62119912 64119910 &&& gm (wpm 62118712 2001198) (P10k.take 183) =
    wem 62118712 62119912 64119910 := by
  decide +kernel

theorem seg_28_1 : SmallGBUpTo 1093 64119910 :=
  small_extend_w (a := 62119910) (A := 62119912) (lo := 62118712) (W := 2001198) seg_28_0
    ⟨31059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_1


end LeanLab.OeSHP2014.Exact1e8
