/-
P0042 GvLtR 1989 ratio check, window 9, even n in [16840002, 18820000], least Goldbach prime at most 733.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_22 : wem 16839269 16840002 18820000 &&& gm (wpm 16839269 1980731) (P10k.take 130) = wem 16839269 16840002 18820000 := by
  decide +kernel

theorem bnd_22 : MinGBBound 16840002 18820000 733 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 130 733 (by decide)) chk_22

theorem lr_22 : (16 + 319633/500000 : ℝ) ≤ Real.log ((16840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((16840002 : ℕ) : ℝ)) 16 (f := (319633/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_22 : (2 + 202941/250000 : ℝ) ≤ Real.log (16 + 319633/500000 : ℝ) := by
  have h := le_log_of (x := (16 + 319633/500000 : ℝ)) 2 (f := (202941/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_22 : ∀ n, Even n → 16840002 ≤ n → n ≤ 18820000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_22 ls_22 (by norm_num) (by norm_num) bnd_22

theorem r2_22 : ∀ n, Even n → 16840002 ≤ n → n ≤ 18820000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_22 ls_22 (by norm_num) (by norm_num) bnd_22

end LeanLab.GvLtR1989
