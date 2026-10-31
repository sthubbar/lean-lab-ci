/-
P0042 GvLtR 1989 ratio check, window 163, even n in [321760002, 323740000], least Goldbach prime at most 971.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_176 : wem 321759031 321760002 323740000 &&& gm (wpm2 321759031 1980969) (P10k.take 164) = wem 321759031 321760002 323740000 := by
  decide +kernel

theorem bnd_176 : MinGBBound 321760002 323740000 971 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 164 971 (by decide)) chk_176

theorem lr_176 : (19 + 117863/200000 : ℝ) ≤ Real.log ((321760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((321760002 : ℕ) : ℝ)) 19 (f := (117863/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_176 : (2 + 974983/1000000 : ℝ) ≤ Real.log (19 + 117863/200000 : ℝ) := by
  have h := le_log_of (x := (19 + 117863/200000 : ℝ)) 2 (f := (974983/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_176 : ∀ n, Even n → 321760002 ≤ n → n ≤ 323740000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_176 ls_176 (by norm_num) (by norm_num) bnd_176

theorem r2_176 : ∀ n, Even n → 321760002 ≤ n → n ≤ 323740000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_176 ls_176 (by norm_num) (by norm_num) bnd_176

end LeanLab.GvLtR1989
