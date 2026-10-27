/-
P0042 GvLtR 1989 ratio check, window 94, even n in [185140002, 187120000], least Goldbach prime at most 859.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_107 : wem 185139143 185140002 187120000 &&& gm (wpm2 185139143 1980857) (P10k.take 149) = wem 185139143 185140002 187120000 := by
  decide +kernel

theorem bnd_107 : MinGBBound 185140002 187120000 859 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 149 859 (by decide)) chk_107

theorem lr_107 : (19 + 36621/1000000 : ℝ) ≤ Real.log ((185140002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((185140002 : ℕ) : ℝ)) 19 (f := (36621/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_107 : (2 + 946363/1000000 : ℝ) ≤ Real.log (19 + 36621/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 36621/1000000 : ℝ)) 2 (f := (946363/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_107 : ∀ n, Even n → 185140002 ≤ n → n ≤ 187120000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_107 ls_107 (by norm_num) (by norm_num) bnd_107

theorem r2_107 : ∀ n, Even n → 185140002 ≤ n → n ≤ 187120000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_107 ls_107 (by norm_num) (by norm_num) bnd_107

end LeanLab.GvLtR1989
