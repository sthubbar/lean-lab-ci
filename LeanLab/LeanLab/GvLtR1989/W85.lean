/-
P0042 GvLtR 1989 ratio check, window 85, even n in [167320002, 169300000], least Goldbach prime at most 823.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_98 : wem 167319179 167320002 169300000 &&& gm (wpm2 167319179 1980821) (P10k.take 143) = wem 167319179 167320002 169300000 := by
  decide +kernel

theorem bnd_98 : MinGBBound 167320002 169300000 823 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 143 823 (by decide)) chk_98

theorem lr_98 : (18 + 935417/1000000 : ℝ) ≤ Real.log ((167320002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((167320002 : ℕ) : ℝ)) 18 (f := (935417/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_98 : (2 + 941033/1000000 : ℝ) ≤ Real.log (18 + 935417/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 935417/1000000 : ℝ)) 2 (f := (941033/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_98 : ∀ n, Even n → 167320002 ≤ n → n ≤ 169300000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_98 ls_98 (by norm_num) (by norm_num) bnd_98

theorem r2_98 : ∀ n, Even n → 167320002 ≤ n → n ≤ 169300000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_98 ls_98 (by norm_num) (by norm_num) bnd_98

end LeanLab.GvLtR1989
