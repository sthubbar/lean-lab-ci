/-
P0042 GvLtR 1989 ratio check, window 122, even n in [240580002, 242560000], least Goldbach prime at most 877.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_135 : wem 240579125 240580002 242560000 &&& gm (wpm2 240579125 1980875) (P10k.take 151) = wem 240579125 240580002 242560000 := by
  decide +kernel

theorem bnd_135 : MinGBBound 240580002 242560000 877 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 151 877 (by decide)) chk_135

theorem lr_135 : (19 + 149281/500000 : ℝ) ≤ Real.log ((240580002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((240580002 : ℕ) : ℝ)) 19 (f := (149281/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_135 : (2 + 960029/1000000 : ℝ) ≤ Real.log (19 + 149281/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 149281/500000 : ℝ)) 2 (f := (960029/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_135 : ∀ n, Even n → 240580002 ≤ n → n ≤ 242560000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_135 ls_135 (by norm_num) (by norm_num) bnd_135

theorem r2_135 : ∀ n, Even n → 240580002 ≤ n → n ≤ 242560000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_135 ls_135 (by norm_num) (by norm_num) bnd_135

end LeanLab.GvLtR1989
