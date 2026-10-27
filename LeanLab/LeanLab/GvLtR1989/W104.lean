/-
P0042 GvLtR 1989 ratio check, window 104, even n in [204940002, 206920000], least Goldbach prime at most 967.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_117 : wem 204939035 204940002 206920000 &&& gm (wpm2 204939035 1980965) (P10k.take 163) = wem 204939035 204940002 206920000 := by
  decide +kernel

theorem bnd_117 : MinGBBound 204940002 206920000 967 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 163 967 (by decide)) chk_117

theorem lr_117 : (19 + 69113/500000 : ℝ) ≤ Real.log ((204940002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((204940002 : ℕ) : ℝ)) 19 (f := (69113/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_117 : (2 + 475843/500000 : ℝ) ≤ Real.log (19 + 69113/500000 : ℝ) := by
  have h := le_log_of (x := (19 + 69113/500000 : ℝ)) 2 (f := (475843/500000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_117 : ∀ n, Even n → 204940002 ≤ n → n ≤ 206920000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_117 ls_117 (by norm_num) (by norm_num) bnd_117

theorem r2_117 : ∀ n, Even n → 204940002 ≤ n → n ≤ 206920000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_117 ls_117 (by norm_num) (by norm_num) bnd_117

end LeanLab.GvLtR1989
