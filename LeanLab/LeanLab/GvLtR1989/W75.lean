/-
P0042 GvLtR 1989 ratio check, window 75, even n in [147520002, 149500000], least Goldbach prime at most 967.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_88 : wem 147519035 147520002 149500000 &&& gm (wpm2 147519035 1980965) (P10k.take 163) = wem 147519035 147520002 149500000 := by
  decide +kernel

theorem bnd_88 : MinGBBound 147520002 149500000 967 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 163 967 (by decide)) chk_88

theorem lr_88 : (18 + 809473/1000000 : ℝ) ≤ Real.log ((147520002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((147520002 : ℕ) : ℝ)) 18 (f := (809473/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_88 : (2 + 934359/1000000 : ℝ) ≤ Real.log (18 + 809473/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 809473/1000000 : ℝ)) 2 (f := (934359/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_88 : ∀ n, Even n → 147520002 ≤ n → n ≤ 149500000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_88 ls_88 (by norm_num) (by norm_num) bnd_88

theorem r2_88 : ∀ n, Even n → 147520002 ≤ n → n ≤ 149500000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_88 ls_88 (by norm_num) (by norm_num) bnd_88

end LeanLab.GvLtR1989
