/-
P0042 GvLtR 1989 ratio check, window 59, even n in [115840002, 117820000], least Goldbach prime at most 751.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_72 : wem 115839251 115840002 117820000 &&& gm (wpm2 115839251 1980749) (P10k.take 133) = wem 115839251 115840002 117820000 := by
  decide +kernel

theorem bnd_72 : MinGBBound 115840002 117820000 751 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 133 751 (by decide)) chk_72

theorem lr_72 : (18 + 567719/1000000 : ℝ) ≤ Real.log ((115840002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((115840002 : ℕ) : ℝ)) 18 (f := (567719/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_72 : (2 + 921423/1000000 : ℝ) ≤ Real.log (18 + 567719/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 567719/1000000 : ℝ)) 2 (f := (921423/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_72 : ∀ n, Even n → 115840002 ≤ n → n ≤ 117820000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_72 ls_72 (by norm_num) (by norm_num) bnd_72

theorem r2_72 : ∀ n, Even n → 115840002 ≤ n → n ≤ 117820000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_72 ls_72 (by norm_num) (by norm_num) bnd_72

end LeanLab.GvLtR1989
