/-
P0042 GvLtR 1989 ratio check, window 53, even n in [103960002, 105940000], least Goldbach prime at most 1009.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_66 : wem 103958993 103960002 105940000 &&& gm (wpm2 103958993 1981007) (P10k.take 169) = wem 103958993 103960002 105940000 := by
  decide +kernel

theorem bnd_66 : MinGBBound 103960002 105940000 1009 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 169 1009 (by decide)) chk_66

theorem lr_66 : (18 + 91903/200000 : ℝ) ≤ Real.log ((103960002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((103960002 : ℕ) : ℝ)) 18 (f := (91903/200000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_66 : (2 + 457789/500000 : ℝ) ≤ Real.log (18 + 91903/200000 : ℝ) := by
  have h := le_log_of (x := (18 + 91903/200000 : ℝ)) 2 (f := (457789/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_66 : ∀ n, Even n → 103960002 ≤ n → n ≤ 105940000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_66 ls_66 (by norm_num) (by norm_num) bnd_66

theorem r2_66 : ∀ n, Even n → 103960002 ≤ n → n ≤ 105940000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_66 ls_66 (by norm_num) (by norm_num) bnd_66

end LeanLab.GvLtR1989
