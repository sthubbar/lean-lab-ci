/-
P0042 GvLtR 1989 ratio check, window 93, even n in [183160002, 185140000], least Goldbach prime at most 1033.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_106 : wem 183158969 183160002 185140000 &&& gm (wpm2 183158969 1981031) (P10k.take 174) = wem 183158969 183160002 185140000 := by
  decide +kernel

theorem bnd_106 : MinGBBound 183160002 185140000 1033 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 174 1033 (by decide)) chk_106

theorem lr_106 : (19 + 25869/1000000 : ℝ) ≤ Real.log ((183160002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((183160002 : ℕ) : ℝ)) 19 (f := (25869/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_106 : (2 + 472899/500000 : ℝ) ≤ Real.log (19 + 25869/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 25869/1000000 : ℝ)) 2 (f := (472899/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_106 : ∀ n, Even n → 183160002 ≤ n → n ≤ 185140000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_106 ls_106 (by norm_num) (by norm_num) bnd_106

theorem r2_106 : ∀ n, Even n → 183160002 ≤ n → n ≤ 185140000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_106 ls_106 (by norm_num) (by norm_num) bnd_106

end LeanLab.GvLtR1989
