/-
P0042 GvLtR 1989 ratio check, window 121, even n in [238600002, 240580000], least Goldbach prime at most 919.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_134 : wem 238599083 238600002 240580000 &&& gm (wpm2 238599083 1980917) (P10k.take 157) = wem 238599083 238600002 240580000 := by
  decide +kernel

theorem bnd_134 : MinGBBound 238600002 240580000 919 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 157 919 (by decide)) chk_134

theorem lr_134 : (19 + 145149/500000 : ℝ) ≤ Real.log ((238600002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((238600002 : ℕ) : ℝ)) 19 (f := (145149/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_134 : (2 + 959601/1000000 : ℝ) ≤ Real.log (19 + 145149/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 145149/500000 : ℝ)) 2 (f := (959601/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_134 : ∀ n, Even n → 238600002 ≤ n → n ≤ 240580000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_134 ls_134 (by norm_num) (by norm_num) bnd_134

theorem r2_134 : ∀ n, Even n → 238600002 ≤ n → n ≤ 240580000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_134 ls_134 (by norm_num) (by norm_num) bnd_134

end LeanLab.GvLtR1989
