/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 4 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail03

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_27_6 : wem 49997738 49998938 51998936 &&& gm (wpm 49997738 2001198) (P10k.take 175) =
    wem 49997738 49998938 51998936 := by
  decide +kernel

theorem seg_27_6 : SmallGBUpTo 1039 51998936 :=
  small_extend_w (a := 49998936) (A := 49998938) (lo := 49997738) (W := 2001198) seg_27_5
    ⟨24999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_6

theorem window_27_7 : wem 51997738 51998938 53998936 &&& gm (wpm 51997738 2001198) (P10k.take 175) =
    wem 51997738 51998938 53998936 := by
  decide +kernel

theorem seg_27_7 : SmallGBUpTo 1039 53998936 :=
  small_extend_w (a := 51998936) (A := 51998938) (lo := 51997738) (W := 2001198) seg_27_6
    ⟨25999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_7


end LeanLab.OeSHP2014.Exact1e8
