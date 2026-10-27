/-
P0042 GvLtR 1989 ratio check, window 139, even n in [274240002, 276220000], least Goldbach prime at most 991.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_152 : wem 274239011 274240002 276220000 &&& gm (wpm2 274239011 1980989) (P10k.take 167) = wem 274239011 274240002 276220000 := by
  decide +kernel

theorem bnd_152 : MinGBBound 274240002 276220000 991 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 167 991 (by decide)) chk_152

theorem lr_152 : (19 + 429513/1000000 : ℝ) ≤ Real.log ((274240002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((274240002 : ℕ) : ℝ)) 19 (f := (429513/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_152 : (2 + 120849/125000 : ℝ) ≤ Real.log (19 + 429513/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 429513/1000000 : ℝ)) 2 (f := (120849/125000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_152 : ∀ n, Even n → 274240002 ≤ n → n ≤ 276220000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_152 ls_152 (by norm_num) (by norm_num) bnd_152

theorem r2_152 : ∀ n, Even n → 274240002 ≤ n → n ≤ 276220000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_152 ls_152 (by norm_num) (by norm_num) bnd_152

end LeanLab.GvLtR1989
