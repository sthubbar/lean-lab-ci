/-
P0042 GvLtR 1989 ratio check, window 27, even n in [52480002, 54460000], least Goldbach prime at most 761.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_40 : wem 52479241 52480002 54460000 &&& gm (wpm 52479241 1980759) (P10k.take 135) = wem 52479241 52480002 54460000 := by
  decide +kernel

theorem bnd_40 : MinGBBound 52480002 54460000 761 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 135 761 (by decide)) chk_40

theorem lr_40 : (17 + 775941/1000000 : ℝ) ≤ Real.log ((52480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((52480002 : ℕ) : ℝ)) 17 (f := (775941/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_40 : (2 + 219461/250000 : ℝ) ≤ Real.log (17 + 775941/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 775941/1000000 : ℝ)) 2 (f := (219461/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_40 : ∀ n, Even n → 52480002 ≤ n → n ≤ 54460000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_40 ls_40 (by norm_num) (by norm_num) bnd_40

theorem r2_40 : ∀ n, Even n → 52480002 ≤ n → n ≤ 54460000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_40 ls_40 (by norm_num) (by norm_num) bnd_40

end LeanLab.GvLtR1989
