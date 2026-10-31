/-
P0042 GvLtR 1989 ratio check, window 146, even n in [288100002, 290080000], least Goldbach prime at most 881.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_159 : wem 288099121 288100002 290080000 &&& gm (wpm2 288099121 1980879) (P10k.take 152) = wem 288099121 288100002 290080000 := by
  decide +kernel

theorem bnd_159 : MinGBBound 288100002 290080000 881 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 152 881 (by decide)) chk_159

theorem lr_159 : (19 + 478817/1000000 : ℝ) ≤ Real.log ((288100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((288100002 : ℕ) : ℝ)) 19 (f := (478817/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_159 : (2 + 484663/500000 : ℝ) ≤ Real.log (19 + 478817/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 478817/1000000 : ℝ)) 2 (f := (484663/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_159 : ∀ n, Even n → 288100002 ≤ n → n ≤ 290080000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_159 ls_159 (by norm_num) (by norm_num) bnd_159

theorem r2_159 : ∀ n, Even n → 288100002 ≤ n → n ≤ 290080000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_159 ls_159 (by norm_num) (by norm_num) bnd_159

end LeanLab.GvLtR1989
