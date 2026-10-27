/-
P0042 GvLtR 1989 ratio check, window 95, even n in [187120002, 189100000], least Goldbach prime at most 1321.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_108 : wem 187118681 187120002 189100000 &&& gm (wpm2 187118681 1981319) (P10k.take 216) = wem 187118681 187120002 189100000 := by
  decide +kernel

theorem bnd_108 : MinGBBound 187120002 189100000 1321 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 216 1321 (by decide)) chk_108

theorem lr_108 : (19 + 47259/1000000 : ℝ) ≤ Real.log ((187120002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((187120002 : ℕ) : ℝ)) 19 (f := (47259/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_108 : (2 + 473461/500000 : ℝ) ≤ Real.log (19 + 47259/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 47259/1000000 : ℝ)) 2 (f := (473461/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_108 : ∀ n, Even n → 187120002 ≤ n → n ≤ 189100000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_108 ls_108 (by norm_num) (by norm_num) bnd_108

theorem r2_108 : ∀ n, Even n → 187120002 ≤ n → n ≤ 189100000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_108 ls_108 (by norm_num) (by norm_num) bnd_108

end LeanLab.GvLtR1989
