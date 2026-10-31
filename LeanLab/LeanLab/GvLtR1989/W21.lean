/-
P0042 GvLtR 1989 ratio check, window 21, even n in [40600002, 42580000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_34 : wem 40599179 40600002 42580000 &&& gm (wpm 40599179 1980821) (P10k.take 143) = wem 40599179 40600002 42580000 := by
  decide +kernel

theorem bnd_34 : MinGBBound 40600002 42580000 823 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_34

theorem lr_34 : (17 + 519277/1000000 : ℝ) ≤ Real.log ((40600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((40600002 : ℕ) : ℝ)) 17 (f := (519277/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_34 : (2 + 8633/10000 : ℝ) ≤ Real.log (17 + 519277/1000000 : ℝ) := by
  have h := le_log_of (x := (17 + 519277/1000000 : ℝ)) 2 (f := (8633/10000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_34 : ∀ n, Even n → 40600002 ≤ n → n ≤ 42580000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_34 ls_34 (by norm_num) (by norm_num) bnd_34

theorem r2_34 : ∀ n, Even n → 40600002 ≤ n → n ≤ 42580000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_34 ls_34 (by norm_num) (by norm_num) bnd_34

end LeanLab.GvLtR1989
