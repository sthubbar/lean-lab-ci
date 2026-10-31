/-
P0042 GvLtR 1989 ratio check, window 46, even n in [90100002, 92080000], least Goldbach prime at most 821.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_59 : wem 90099181 90100002 92080000 &&& gm (wpm 90099181 1980819) (P10k.take 142) = wem 90099181 90100002 92080000 := by
  decide +kernel

theorem bnd_59 : MinGBBound 90100002 92080000 821 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 142 821 (by decide)) chk_59

theorem lr_59 : (18 + 316429/1000000 : ℝ) ≤ Real.log ((90100002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((90100002 : ℕ) : ℝ)) 18 (f := (316429/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_59 : (2 + 907797/1000000 : ℝ) ≤ Real.log (18 + 316429/1000000 : ℝ) := by
  have h := le_log_of (x := (18 + 316429/1000000 : ℝ)) 2 (f := (907797/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_59 : ∀ n, Even n → 90100002 ≤ n → n ≤ 92080000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_59 ls_59 (by norm_num) (by norm_num) bnd_59

theorem r2_59 : ∀ n, Even n → 90100002 ≤ n → n ≤ 92080000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_59 ls_59 (by norm_num) (by norm_num) bnd_59

end LeanLab.GvLtR1989
