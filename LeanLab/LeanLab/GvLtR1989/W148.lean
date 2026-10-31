/-
P0042 GvLtR 1989 ratio check, window 148, even n in [292060002, 294040000], least Goldbach prime at most 859.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_161 : wem 292059143 292060002 294040000 &&& gm (wpm2 292059143 1980857) (P10k.take 149) = wem 292059143 292060002 294040000 := by
  decide +kernel

theorem bnd_161 : MinGBBound 292060002 294040000 859 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 149 859 (by decide)) chk_161

theorem lr_161 : (19 + 123117/250000 : ℝ) ≤ Real.log ((292060002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((292060002 : ℕ) : ℝ)) 19 (f := (123117/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_161 : (2 + 970027/1000000 : ℝ) ≤ Real.log (19 + 123117/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 123117/250000 : ℝ)) 2 (f := (970027/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_161 : ∀ n, Even n → 292060002 ≤ n → n ≤ 294040000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_161 ls_161 (by norm_num) (by norm_num) bnd_161

theorem r2_161 : ∀ n, Even n → 292060002 ≤ n → n ≤ 294040000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_161 ls_161 (by norm_num) (by norm_num) bnd_161

end LeanLab.GvLtR1989
