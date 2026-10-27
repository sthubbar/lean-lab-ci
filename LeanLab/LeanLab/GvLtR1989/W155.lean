/-
P0042 GvLtR 1989 ratio check, window 155, even n in [305920002, 307900000], least Goldbach prime at most 1021.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_168 : wem 305918981 305920002 307900000 &&& gm (wpm2 305918981 1981019) (P10k.take 172) = wem 305918981 305920002 307900000 := by
  decide +kernel

theorem bnd_168 : MinGBBound 305920002 307900000 1021 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 172 1021 (by decide)) chk_168

theorem lr_168 : (19 + 538833/1000000 : ℝ) ≤ Real.log ((305920002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((305920002 : ℕ) : ℝ)) 19 (f := (538833/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_168 : (2 + 486201/500000 : ℝ) ≤ Real.log (19 + 538833/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 538833/1000000 : ℝ)) 2 (f := (486201/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_168 : ∀ n, Even n → 305920002 ≤ n → n ≤ 307900000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_168 ls_168 (by norm_num) (by norm_num) bnd_168

theorem r2_168 : ∀ n, Even n → 305920002 ≤ n → n ≤ 307900000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_168 ls_168 (by norm_num) (by norm_num) bnd_168

end LeanLab.GvLtR1989
