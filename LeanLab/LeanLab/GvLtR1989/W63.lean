/-
P0042 GvLtR 1989 ratio check, window 63, even n in [123760002, 125740000], least Goldbach prime at most 953.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_76 : wem 123759049 123760002 125740000 &&& gm (wpm2 123759049 1980951) (P10k.take 162) = wem 123759049 123760002 125740000 := by
  decide +kernel

theorem bnd_76 : MinGBBound 123760002 125740000 953 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 162 953 (by decide)) chk_76

theorem lr_76 : (18 + 633853/1000000 : ℝ) ≤ Real.log ((123760002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((123760002 : ℕ) : ℝ)) 18 (f := (633853/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_76 : (2 + 462489/500000 : ℝ) ≤ Real.log (18 + 633853/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 633853/1000000 : ℝ)) 2 (f := (462489/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_76 : ∀ n, Even n → 123760002 ≤ n → n ≤ 125740000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_76 ls_76 (by norm_num) (by norm_num) bnd_76

theorem r2_76 : ∀ n, Even n → 123760002 ≤ n → n ≤ 125740000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_76 ls_76 (by norm_num) (by norm_num) bnd_76

end LeanLab.GvLtR1989
