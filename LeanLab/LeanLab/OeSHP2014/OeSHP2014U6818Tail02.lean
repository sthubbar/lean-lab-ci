/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 2 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail01

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_27_2 : wem 41997738 41998938 43998936 &&& gm (wpm 41997738 2001198) (P10k.take 175) =
    wem 41997738 41998938 43998936 := by
  decide +kernel

theorem seg_27_2 : SmallGBUpTo 1039 43998936 :=
  small_extend_w (a := 41998936) (A := 41998938) (lo := 41997738) (W := 2001198) seg_27_1
    ⟨20999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_2

theorem window_27_3 : wem 43997738 43998938 45998936 &&& gm (wpm 43997738 2001198) (P10k.take 175) =
    wem 43997738 43998938 45998936 := by
  decide +kernel

theorem seg_27_3 : SmallGBUpTo 1039 45998936 :=
  small_extend_w (a := 43998936) (A := 43998938) (lo := 43997738) (W := 2001198) seg_27_2
    ⟨21999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_3


end LeanLab.OeSHP2014.Exact1e8
