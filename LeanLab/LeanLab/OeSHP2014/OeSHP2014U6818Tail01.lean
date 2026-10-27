/-
U-6818, P0005, Table 4 record gaps 27 and 28, part 1 of 16: windows of at most 2000000,
at most 2 per module to keep the kernel's memory low. Namespace Exact1e8 as in Seg23 to Seg26.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Seg26

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_27 : ∀ q ∈ P10k.take 175, q ≤ 1039 := by
  have h : (P10k.take 175).all (fun q => decide (q ≤ 1039)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem window_27_0 : wem 37997738 37998938 39998936 &&& gm (wpm 37997738 2001198) (P10k.take 175) =
    wem 37997738 37998938 39998936 := by
  decide +kernel

theorem seg_27_0 : SmallGBUpTo 1039 39998936 :=
  small_extend_w (a := 37998936) (A := 37998938) (lo := 37997738) (W := 2001198) (small_bound_mono seg_26 (by norm_num))
    ⟨18999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_0

theorem window_27_1 : wem 39997738 39998938 41998936 &&& gm (wpm 39997738 2001198) (P10k.take 175) =
    wem 39997738 39998938 41998936 := by
  decide +kernel

theorem seg_27_1 : SmallGBUpTo 1039 41998936 :=
  small_extend_w (a := 39998936) (A := 39998938) (lo := 39997738) (W := 2001198) seg_27_0
    ⟨19999468, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 175) take_le_27 window_27_1


end LeanLab.OeSHP2014.Exact1e8
