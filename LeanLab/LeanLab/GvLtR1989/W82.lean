/-
P0042 GvLtR 1989 ratio check, window 82, even n in [161380002, 163360000], least Goldbach prime at most 967.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_95 : wem 161379035 161380002 163360000 &&& gm (wpm2 161379035 1980965) (P10k.take 163) = wem 161379035 161380002 163360000 := by
  decide +kernel

theorem bnd_95 : MinGBBound 161380002 163360000 967 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 163 967 (by decide)) chk_95

theorem lr_95 : (18 + 899271/1000000 : ℝ) ≤ Real.log ((161380002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((161380002 : ℕ) : ℝ)) 18 (f := (899271/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_95 : (2 + 469561/500000 : ℝ) ≤ Real.log (18 + 899271/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 899271/1000000 : ℝ)) 2 (f := (469561/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_95 : ∀ n, Even n → 161380002 ≤ n → n ≤ 163360000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_95 ls_95 (by norm_num) (by norm_num) bnd_95

theorem r2_95 : ∀ n, Even n → 161380002 ≤ n → n ≤ 163360000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_95 ls_95 (by norm_num) (by norm_num) bnd_95

end LeanLab.GvLtR1989
