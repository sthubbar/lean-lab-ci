/-
P0042 GvLtR 1989 ratio check, window 39, even n in [76240002, 78220000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_52 : wem 76239251 76240002 78220000 &&& gm (wpm 76239251 1980749) (P10k.take 133) = wem 76239251 76240002 78220000 := by
  decide +kernel

theorem bnd_52 : MinGBBound 76240002 78220000 751 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_52

theorem lr_52 : (18 + 29879/200000 : ℝ) ≤ Real.log ((76240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((76240002 : ℕ) : ℝ)) 18 (f := (29879/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_52 : (2 + 224659/250000 : ℝ) ≤ Real.log (18 + 29879/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 29879/200000 : ℝ)) 2 (f := (224659/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_52 : ∀ n, Even n → 76240002 ≤ n → n ≤ 78220000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_52 ls_52 (by norm_num) (by norm_num) bnd_52

theorem r2_52 : ∀ n, Even n → 76240002 ≤ n → n ≤ 78220000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_52 ls_52 (by norm_num) (by norm_num) bnd_52

end LeanLab.GvLtR1989
