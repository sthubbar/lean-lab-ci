/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 10 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail09

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_28_6 : wem 72118712 72119912 74119910 &&& gm (wpm 72118712 2001198) (P10k.take 183) =
    wem 72118712 72119912 74119910 := by
  decide +kernel

theorem seg_28_6 : SmallGBUpTo 1093 74119910 :=
  small_extend_w (a := 72119910) (A := 72119912) (lo := 72118712) (W := 2001198) seg_28_5
    ⟨36059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_6

theorem window_28_7 : wem 74118712 74119912 76119910 &&& gm (wpm 74118712 2001198) (P10k.take 183) =
    wem 74118712 74119912 76119910 := by
  decide +kernel

theorem seg_28_7 : SmallGBUpTo 1093 76119910 :=
  small_extend_w (a := 74119910) (A := 74119912) (lo := 74118712) (W := 2001198) seg_28_6
    ⟨37059955, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 183) take_le_28 window_28_7


end LeanLab.OeSHP2014.Exact1e8
