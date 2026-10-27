/-
U-6818, P0005, Table 4 record gap 25: SmallGBUpTo for the row's p up to the next row,
windows of at most 2000000, part of OeSHP2014U6818Exact1e8.lean. AI-written Lean code, Claude,
2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.OeSHP2014U6818Seg24

namespace LeanLab.OeSHP2014.Exact1e8

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_25 : ∀ q ∈ P10k.take 158, q ≤ 929 := by
  have h : (P10k.take 158).all (fun q => decide (q ≤ 929)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem window_25_0 : wem 24105682 24106882 26106880 &&& gm (wpm 24105682 2001198) (P10k.take 158) =
    wem 24105682 24106882 26106880 := by
  decide +kernel

theorem seg_25_0 : SmallGBUpTo 929 26106880 :=
  small_extend_w (a := 24106880) (A := 24106882) (lo := 24105682) (W := 2001198) (small_bound_mono seg_24 (by norm_num))
    ⟨12053440, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 158) take_le_25 window_25_0

theorem window_25_1 : wem 26105682 26106882 27789876 &&& gm (wpm 26105682 1684194) (P10k.take 158) =
    wem 26105682 26106882 27789876 := by
  decide +kernel

theorem seg_25_1 : SmallGBUpTo 929 27789876 :=
  small_extend_w (a := 26106880) (A := 26106882) (lo := 26105682) (W := 1684194) seg_25_0
    ⟨13053440, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (take_prime 158) take_le_25 window_25_1

theorem seg_25 : SmallGBUpTo 929 27789876 := seg_25_1


end LeanLab.OeSHP2014.Exact1e8
