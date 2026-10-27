/-
P0042 GvLtR 1989 ratio check, window 153, even n in [301960002, 303940000], least Goldbach prime at most 829.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_166 : wem 301959173 301960002 303940000 &&& gm (wpm2 301959173 1980827) (P10k.take 145) = wem 301959173 301960002 303940000 := by
  decide +kernel

theorem bnd_166 : MinGBBound 301960002 303940000 829 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 145 829 (by decide)) chk_166

theorem lr_166 : (19 + 131451/250000 : ℝ) ≤ Real.log ((301960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((301960002 : ℕ) : ℝ)) 19 (f := (131451/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_166 : (2 + 194347/200000 : ℝ) ≤ Real.log (19 + 131451/250000 : ℝ) := by
  have h := le_log_of (x := (19 + 131451/250000 : ℝ)) 2 (f := (194347/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_166 : ∀ n, Even n → 301960002 ≤ n → n ≤ 303940000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_166 ls_166 (by norm_num) (by norm_num) bnd_166

theorem r2_166 : ∀ n, Even n → 301960002 ≤ n → n ≤ 303940000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_166 ls_166 (by norm_num) (by norm_num) bnd_166

end LeanLab.GvLtR1989
