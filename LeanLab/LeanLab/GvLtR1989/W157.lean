/-
P0042 GvLtR 1989 ratio check, window 157, even n in [309880002, 311860000], least Goldbach prime at most 1021.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_170 : wem 309878981 309880002 311860000 &&& gm (wpm2 309878981 1981019) (P10k.take 172) = wem 309878981 309880002 311860000 := by
  decide +kernel

theorem bnd_170 : MinGBBound 309880002 311860000 1021 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 172 1021 (by decide)) chk_170

theorem lr_170 : (19 + 275847/500000 : ℝ) ≤ Real.log ((309880002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((309880002 : ℕ) : ℝ)) 19 (f := (275847/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_170 : (2 + 48653/50000 : ℝ) ≤ Real.log (19 + 275847/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 275847/500000 : ℝ)) 2 (f := (48653/50000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_170 : ∀ n, Even n → 309880002 ≤ n → n ≤ 311860000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_170 ls_170 (by norm_num) (by norm_num) bnd_170

theorem r2_170 : ∀ n, Even n → 309880002 ≤ n → n ≤ 311860000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_170 ls_170 (by norm_num) (by norm_num) bnd_170

end LeanLab.GvLtR1989
