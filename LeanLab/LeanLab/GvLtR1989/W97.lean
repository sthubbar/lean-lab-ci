/-
P0042 GvLtR 1989 ratio check, window 97, even n in [191080002, 193060000], least Goldbach prime at most 911.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_110 : wem 191079091 191080002 193060000 &&& gm (wpm2 191079091 1980909) (P10k.take 156) = wem 191079091 191080002 193060000 := by
  decide +kernel

theorem bnd_110 : MinGBBound 191080002 193060000 911 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 156 911 (by decide)) chk_110

theorem lr_110 : (19 + 68201/1000000 : ℝ) ≤ Real.log ((191080002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((191080002 : ℕ) : ℝ)) 19 (f := (68201/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_110 : (2 + 948021/1000000 : ℝ) ≤ Real.log (19 + 68201/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 68201/1000000 : ℝ)) 2 (f := (948021/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_110 : ∀ n, Even n → 191080002 ≤ n → n ≤ 193060000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_110 ls_110 (by norm_num) (by norm_num) bnd_110

theorem r2_110 : ∀ n, Even n → 191080002 ≤ n → n ≤ 193060000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_110 ls_110 (by norm_num) (by norm_num) bnd_110

end LeanLab.GvLtR1989
