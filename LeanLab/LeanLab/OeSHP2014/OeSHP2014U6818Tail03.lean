/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 3 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail02

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_27_4 : wem 45997738 45998938 47998936 &&& gm (wpm 45997738 2001198) (P10k.take 175) =
    wem 45997738 45998938 47998936 := by
  decide +kernel

theorem seg_27_4 : SmallGBUpTo 1039 47998936 :=
  small_extend_w (a := 45998936) (A := 45998938) (lo := 45997738) (W := 2001198) seg_27_3
    ⟨22999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_4

theorem window_27_5 : wem 47997738 47998938 49998936 &&& gm (wpm 47997738 2001198) (P10k.take 175) =
    wem 47997738 47998938 49998936 := by
  decide +kernel

theorem seg_27_5 : SmallGBUpTo 1039 49998936 :=
  small_extend_w (a := 47998936) (A := 47998938) (lo := 47997738) (W := 2001198) seg_27_4
    ⟨23999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_5


end LeanLab.OeSHP2014.Exact1e8
