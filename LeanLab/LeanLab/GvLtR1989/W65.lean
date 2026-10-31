/-
P0042 GvLtR 1989 ratio check, window 65, even n in [127720002, 129700000], least Goldbach prime at most 881.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_78 : wem 127719121 127720002 129700000 &&& gm (wpm2 127719121 1980879) (P10k.take 152) = wem 127719121 127720002 129700000 := by
  decide +kernel

theorem bnd_78 : MinGBBound 127720002 129700000 881 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 152 881 (by decide)) chk_78

theorem lr_78 : (18 + 665349/1000000 : ℝ) ≤ Real.log ((127720002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((127720002 : ℕ) : ℝ)) 18 (f := (665349/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_78 : (2 + 926667/1000000 : ℝ) ≤ Real.log (18 + 665349/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 665349/1000000 : ℝ)) 2 (f := (926667/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_78 : ∀ n, Even n → 127720002 ≤ n → n ≤ 129700000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_78 ls_78 (by norm_num) (by norm_num) bnd_78

theorem r2_78 : ∀ n, Even n → 127720002 ≤ n → n ≤ 129700000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_78 ls_78 (by norm_num) (by norm_num) bnd_78

end LeanLab.GvLtR1989
