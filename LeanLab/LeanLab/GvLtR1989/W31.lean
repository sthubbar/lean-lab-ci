/-
P0042 GvLtR 1989 ratio check, window 31, even n in [60400002, 62380000], least Goldbach prime at most 769.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_44 : wem 60399233 60400002 62380000 &&& gm (wpm 60399233 1980767) (P10k.take 136) = wem 60399233 60400002 62380000 := by
  decide +kernel

theorem bnd_44 : MinGBBound 60400002 62380000 769 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 136 769 (by decide)) chk_44

theorem lr_44 : (17 + 458249/500000 : ℝ) ≤ Real.log ((60400002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((60400002 : ℕ) : ℝ)) 17 (f := (458249/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_44 : (2 + 22143/25000 : ℝ) ≤ Real.log (17 + 458249/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 458249/500000 : ℝ)) 2 (f := (22143/25000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_44 : ∀ n, Even n → 60400002 ≤ n → n ≤ 62380000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_44 ls_44 (by norm_num) (by norm_num) bnd_44

theorem r2_44 : ∀ n, Even n → 60400002 ≤ n → n ≤ 62380000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_44 ls_44 (by norm_num) (by norm_num) bnd_44

end LeanLab.GvLtR1989
