/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 6 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Tail05

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem window_27_10 : wem 57997738 57998938 59998936 &&& gm (wpm 57997738 2001198) (P10k.take 175) =
    wem 57997738 57998938 59998936 := by
  decide +kernel

theorem seg_27_10 : SmallGBUpTo 1039 59998936 :=
  small_extend_w (a := 57998936) (A := 57998938) (lo := 57997738) (W := 2001198) seg_27_9
    ⟨28999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_10

theorem window_27_11 : wem 59997738 59998938 60119910 &&& gm (wpm 59997738 122172) (P10k.take 175) =
    wem 59997738 59998938 60119910 := by
  decide +kernel

theorem seg_27_11 : SmallGBUpTo 1039 60119910 :=
  small_extend_w (a := 59998936) (A := 59998938) (lo := 59997738) (W := 122172) seg_27_10
    ⟨29999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_11

theorem seg_27 : SmallGBUpTo 1039 60119910 := seg_27_11

theorem take_le_28 : ∀ q ∈ P10k.take 183, q ≤ 1093 := by
  have h : (P10k.take 183).all (fun q => decide (q ≤ 1093)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq


end LeanLab.OeSHP2014.Exact1e8
