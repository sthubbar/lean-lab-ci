/-
U-6818, P0005, Table 4 record gap 24: SmallGBUpTo for the row's p up to the next row,
windows of at most 2000000, part of OeSHP2014U6818Exact1e8.lean. AI-written Lean code, Claude,
2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Seg23

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_24 : ∀ q ∈ P10k.take 145, q ≤ 829 := by
  have h : (P10k.take 145).all (fun q => decide (q ≤ 829)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem window_24_0 : wem 10758722 10759922 12759920 &&& gm (wpm 10758722 2001198) (P10k.take 145) =
    wem 10758722 10759922 12759920 := by
  decide +kernel

theorem seg_24_0 : SmallGBUpTo 829 12759920 :=
  small_extend_w (a := 10759920) (A := 10759922) (lo := 10758722) (W := 2001198) (small_bound_mono seg_23 (by norm_num))
    ⟨5379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_0

theorem window_24_1 : wem 12758722 12759922 14759920 &&& gm (wpm 12758722 2001198) (P10k.take 145) =
    wem 12758722 12759922 14759920 := by
  decide +kernel

theorem seg_24_1 : SmallGBUpTo 829 14759920 :=
  small_extend_w (a := 12759920) (A := 12759922) (lo := 12758722) (W := 2001198) seg_24_0
    ⟨6379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_1

theorem window_24_2 : wem 14758722 14759922 16759920 &&& gm (wpm 14758722 2001198) (P10k.take 145) =
    wem 14758722 14759922 16759920 := by
  decide +kernel

theorem seg_24_2 : SmallGBUpTo 829 16759920 :=
  small_extend_w (a := 14759920) (A := 14759922) (lo := 14758722) (W := 2001198) seg_24_1
    ⟨7379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_2

theorem window_24_3 : wem 16758722 16759922 18759920 &&& gm (wpm 16758722 2001198) (P10k.take 145) =
    wem 16758722 16759922 18759920 := by
  decide +kernel

theorem seg_24_3 : SmallGBUpTo 829 18759920 :=
  small_extend_w (a := 16759920) (A := 16759922) (lo := 16758722) (W := 2001198) seg_24_2
    ⟨8379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_3

theorem window_24_4 : wem 18758722 18759922 20759920 &&& gm (wpm 18758722 2001198) (P10k.take 145) =
    wem 18758722 18759922 20759920 := by
  decide +kernel

theorem seg_24_4 : SmallGBUpTo 829 20759920 :=
  small_extend_w (a := 18759920) (A := 18759922) (lo := 18758722) (W := 2001198) seg_24_3
    ⟨9379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_4

theorem window_24_5 : wem 20758722 20759922 22759920 &&& gm (wpm 20758722 2001198) (P10k.take 145) =
    wem 20758722 20759922 22759920 := by
  decide +kernel

theorem seg_24_5 : SmallGBUpTo 829 22759920 :=
  small_extend_w (a := 20759920) (A := 20759922) (lo := 20758722) (W := 2001198) seg_24_4
    ⟨10379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_5

theorem window_24_6 : wem 22758722 22759922 24106880 &&& gm (wpm 22758722 1348158) (P10k.take 145) =
    wem 22758722 22759922 24106880 := by
  decide +kernel

theorem seg_24_6 : SmallGBUpTo 829 24106880 :=
  small_extend_w (a := 22759920) (A := 22759922) (lo := 22758722) (W := 1348158) seg_24_5
    ⟨11379960, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 145) take_le_24 window_24_6

theorem seg_24 : SmallGBUpTo 829 24106880 := seg_24_6


end LeanLab.OeSHP2014.Exact1e8
