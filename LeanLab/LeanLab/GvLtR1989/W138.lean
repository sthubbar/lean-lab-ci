/-
P0042 GvLtR 1989 ratio check, window 138, even n in [272260002, 274240000], least Goldbach prime at most 1129.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_151 : wem 272258873 272260002 274240000 &&& gm (wpm2 272258873 1981127) (P10k.take 189) = wem 272258873 272260002 274240000 := by
  decide +kernel

theorem bnd_151 : MinGBBound 272260002 274240000 1129 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 189 1129 (by decide)) chk_151

theorem lr_151 : (19 + 422267/1000000 : ℝ) ≤ Real.log ((272260002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((272260002 : ℕ) : ℝ)) 19 (f := (422267/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_151 : (2 + 966419/1000000 : ℝ) ≤ Real.log (19 + 422267/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 422267/1000000 : ℝ)) 2 (f := (966419/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_151 : ∀ n, Even n → 272260002 ≤ n → n ≤ 274240000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_151 ls_151 (by norm_num) (by norm_num) bnd_151

theorem r2_151 : ∀ n, Even n → 272260002 ≤ n → n ≤ 274240000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_151 ls_151 (by norm_num) (by norm_num) bnd_151

end LeanLab.GvLtR1989
