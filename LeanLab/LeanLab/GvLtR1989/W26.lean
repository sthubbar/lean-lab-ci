/-
P0042 GvLtR 1989 ratio check, window 26, even n in [50500002, 52480000], least Goldbach prime at most 821.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_39 : wem 50499181 50500002 52480000 &&& gm (wpm 50499181 1980819) (P10k.take 142) = wem 50499181 50500002 52480000 := by
  decide +kernel

theorem bnd_39 : MinGBBound 50500002 52480000 821 :=
  bound_of_wcheck (by norm_num) (by norm_num) (by norm_num) (by decide) (take_le 142 821 (by decide)) chk_39

theorem lr_39 : (17 + 368741/500000 : ℝ) ≤ Real.log ((50500002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((50500002 : ℕ) : ℝ)) 17 (f := (368741/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_39 : (2 + 875679/1000000 : ℝ) ≤ Real.log (17 + 368741/500000 : ℝ) := by
  have h := le_log_of (x := (17 + 368741/500000 : ℝ)) 2 (f := (875679/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_39 : ∀ n, Even n → 50500002 ≤ n → n ≤ 52480000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_39 ls_39 (by norm_num) (by norm_num) bnd_39

theorem r2_39 : ∀ n, Even n → 50500002 ≤ n → n ≤ 52480000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_39 ls_39 (by norm_num) (by norm_num) bnd_39

end LeanLab.GvLtR1989
