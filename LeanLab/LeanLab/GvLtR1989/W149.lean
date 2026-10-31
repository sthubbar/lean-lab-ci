/-
P0042 GvLtR 1989 ratio check, window 149, even n in [294040002, 296020000], least Goldbach prime at most 1033.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_162 : wem 294038969 294040002 296020000 &&& gm (wpm2 294038969 1981031) (P10k.take 174) = wem 294038969 294040002 296020000 := by
  decide +kernel

theorem bnd_162 : MinGBBound 294040002 296020000 1033 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 174 1033 (by decide)) chk_162

theorem lr_162 : (19 + 19969/40000 : ℝ) ≤ Real.log ((294040002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((294040002 : ℕ) : ℝ)) 19 (f := (19969/40000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_162 : (2 + 970373/1000000 : ℝ) ≤ Real.log (19 + 19969/40000 : ℝ) := by
  have h := le_log_of (x := (19 + 19969/40000 : ℝ)) 2 (f := (970373/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_162 : ∀ n, Even n → 294040002 ≤ n → n ≤ 296020000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_162 ls_162 (by norm_num) (by norm_num) bnd_162

theorem r2_162 : ∀ n, Even n → 294040002 ≤ n → n ≤ 296020000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_162 ls_162 (by norm_num) (by norm_num) bnd_162

end LeanLab.GvLtR1989
