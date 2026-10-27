/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 5 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail04

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_27_8 : wem 53997738 53998938 55998936 &&& gm (wpm 53997738 2001198) (P10k.take 175) =
    wem 53997738 53998938 55998936 := by
  decide +kernel

theorem seg_27_8 : SmallGBUpTo 1039 55998936 :=
  small_extend_w (a := 53998936) (A := 53998938) (lo := 53997738) (W := 2001198) seg_27_7
    ⟨26999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_8

theorem window_27_9 : wem 55997738 55998938 57998936 &&& gm (wpm 55997738 2001198) (P10k.take 175) =
    wem 55997738 55998938 57998936 := by
  decide +kernel

theorem seg_27_9 : SmallGBUpTo 1039 57998936 :=
  small_extend_w (a := 55998936) (A := 55998938) (lo := 55997738) (W := 2001198) seg_27_8
    ⟨27999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_9


end LeanLab.OeSHP2014.Exact1e8
