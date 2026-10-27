/-
P0042 GvLtR 1989 ratio check, window 17, even n in [32680002, 34660000], least Goldbach prime at most 769.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_30 : wem 32679233 32680002 34660000 &&& gm (wpm 32679233 1980767) (P10k.take 136) = wem 32679233 32680002 34660000 := by
  decide +kernel

theorem bnd_30 : MinGBBound 32680002 34660000 769 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 136 769 (by decide)) chk_30

theorem lr_30 : (17 + 4723/15625 : ℝ) ≤ Real.log ((32680002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((32680002 : ℕ) : ℝ)) 17 (f := (4723/15625 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_30 : (2 + 212709/250000 : ℝ) ≤ Real.log (17 + 4723/15625 : ℝ) := by
  have h := le_log_of (x := (17 + 4723/15625 : ℝ)) 2 (f := (212709/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_30 : ∀ n, Even n → 32680002 ≤ n → n ≤ 34660000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_30 ls_30 (by norm_num) (by norm_num) bnd_30

theorem r2_30 : ∀ n, Even n → 32680002 ≤ n → n ≤ 34660000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_30 ls_30 (by norm_num) (by norm_num) bnd_30

end LeanLab.GvLtR1989
