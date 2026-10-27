/-
P0042 GvLtR 1989 ratio check, window 126, even n in [248500002, 250480000], least Goldbach prime at most 1013.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_139 : wem 248498989 248500002 250480000 &&& gm (wpm2 248498989 1981011) (P10k.take 170) = wem 248498989 248500002 250480000 := by
  decide +kernel

theorem bnd_139 : MinGBBound 248500002 250480000 1013 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 170 1013 (by decide)) chk_139

theorem lr_139 : (19 + 41369/125000 : ℝ) ≤ Real.log ((248500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((248500002 : ℕ) : ℝ)) 19 (f := (41369/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_139 : (2 + 480853/500000 : ℝ) ≤ Real.log (19 + 41369/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 41369/125000 : ℝ)) 2 (f := (480853/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_139 : ∀ n, Even n → 248500002 ≤ n → n ≤ 250480000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_139 ls_139 (by norm_num) (by norm_num) bnd_139

theorem r2_139 : ∀ n, Even n → 248500002 ≤ n → n ≤ 250480000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_139 ls_139 (by norm_num) (by norm_num) bnd_139

end LeanLab.GvLtR1989
