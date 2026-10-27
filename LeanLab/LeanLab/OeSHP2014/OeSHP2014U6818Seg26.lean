/-
U-6818, P0005, Table 4 record gap 26: SmallGBUpTo for the row's p up to the next row,
windows of at most 2000000, part of OeSHP2014U6818Exact1e8.lean. AI-written Lean code, Claude,
2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Seg25

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_26 : ∀ q ∈ P10k.take 168, q ≤ 997 := by
  have h : (P10k.take 168).all (fun q => decide (q ≤ 997)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem window_26_0 : wem 27788678 27789878 29789876 &&& gm (wpm 27788678 2001198) (P10k.take 168) =
    wem 27788678 27789878 29789876 := by
  decide +kernel

theorem seg_26_0 : SmallGBUpTo 997 29789876 :=
  small_extend_w (a := 27789876) (A := 27789878) (lo := 27788678) (W := 2001198) (small_bound_mono seg_25 (by norm_num))
    ⟨13894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_0

theorem window_26_1 : wem 29788678 29789878 31789876 &&& gm (wpm 29788678 2001198) (P10k.take 168) =
    wem 29788678 29789878 31789876 := by
  decide +kernel

theorem seg_26_1 : SmallGBUpTo 997 31789876 :=
  small_extend_w (a := 29789876) (A := 29789878) (lo := 29788678) (W := 2001198) seg_26_0
    ⟨14894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_1

theorem window_26_2 : wem 31788678 31789878 33789876 &&& gm (wpm 31788678 2001198) (P10k.take 168) =
    wem 31788678 31789878 33789876 := by
  decide +kernel

theorem seg_26_2 : SmallGBUpTo 997 33789876 :=
  small_extend_w (a := 31789876) (A := 31789878) (lo := 31788678) (W := 2001198) seg_26_1
    ⟨15894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_2

theorem window_26_3 : wem 33788678 33789878 35789876 &&& gm (wpm 33788678 2001198) (P10k.take 168) =
    wem 33788678 33789878 35789876 := by
  decide +kernel

theorem seg_26_3 : SmallGBUpTo 997 35789876 :=
  small_extend_w (a := 33789876) (A := 33789878) (lo := 33788678) (W := 2001198) seg_26_2
    ⟨16894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_3

theorem window_26_4 : wem 35788678 35789878 37789876 &&& gm (wpm 35788678 2001198) (P10k.take 168) =
    wem 35788678 35789878 37789876 := by
  decide +kernel

theorem seg_26_4 : SmallGBUpTo 997 37789876 :=
  small_extend_w (a := 35789876) (A := 35789878) (lo := 35788678) (W := 2001198) seg_26_3
    ⟨17894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_4

theorem window_26_5 : wem 37788678 37789878 37998936 &&& gm (wpm 37788678 210258) (P10k.take 168) =
    wem 37788678 37789878 37998936 := by
  decide +kernel

theorem seg_26_5 : SmallGBUpTo 997 37998936 :=
  small_extend_w (a := 37789876) (A := 37789878) (lo := 37788678) (W := 210258) seg_26_4
    ⟨18894938, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 168) take_le_26 window_26_5

theorem seg_26 : SmallGBUpTo 997 37998936 := seg_26_5


end LeanLab.OeSHP2014.Exact1e8
