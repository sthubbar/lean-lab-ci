/-
P0042 GvLtR 1989 ratio check, window 69, even n in [135640002, 137620000], least Goldbach prime at most 971.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_82 : wem 135639031 135640002 137620000 &&& gm (wpm2 135639031 1980969) (P10k.take 164) = wem 135639031 135640002 137620000 := by
  decide +kernel

theorem bnd_82 : MinGBBound 135640002 137620000 971 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 164 971 (by decide)) chk_82

theorem lr_82 : (18 + 725513/1000000 : ℝ) ≤ Real.log ((135640002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((135640002 : ℕ) : ℝ)) 18 (f := (725513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_82 : (2 + 185977/200000 : ℝ) ≤ Real.log (18 + 725513/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 725513/1000000 : ℝ)) 2 (f := (185977/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_82 : ∀ n, Even n → 135640002 ≤ n → n ≤ 137620000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_82 ls_82 (by norm_num) (by norm_num) bnd_82

theorem r2_82 : ∀ n, Even n → 135640002 ≤ n → n ≤ 137620000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_82 ls_82 (by norm_num) (by norm_num) bnd_82

end LeanLab.GvLtR1989
