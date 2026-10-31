/-
P0042 GvLtR 1989 ratio check, window 127, even n in [250480002, 252460000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_140 : wem 250478993 250480002 252460000 &&& gm (wpm2 250478993 1981007) (P10k.take 169) = wem 250478993 250480002 252460000 := by
  decide +kernel

theorem bnd_140 : MinGBBound 250480002 252460000 1009 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_140

theorem lr_140 : (19 + 42361/125000 : ℝ) ≤ Real.log ((250480002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((250480002 : ℕ) : ℝ)) 19 (f := (42361/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_140 : (2 + 240529/250000 : ℝ) ≤ Real.log (19 + 42361/125000 : ℝ) := by
  have h := le_log_of (x := (19 + 42361/125000 : ℝ)) 2 (f := (240529/250000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_140 : ∀ n, Even n → 250480002 ≤ n → n ≤ 252460000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_140 ls_140 (by norm_num) (by norm_num) bnd_140

theorem r2_140 : ∀ n, Even n → 250480002 ≤ n → n ≤ 252460000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_140 ls_140 (by norm_num) (by norm_num) bnd_140

end LeanLab.GvLtR1989
