/-
P0042 GvLtR 1989 ratio check, window 151, even n in [298000002, 299980000], least Goldbach prime at most 1031.
AI-written Lean code, Claude, 2026-10-17, run 20261017T2303Z-3715. Binary Goldbach is OPEN.
-/
import LeanLab.GvLtR1989.Base

namespace LeanLab.GvLtR1989

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem chk_164 : wem 297998971 298000002 299980000 &&& gm (wpm2 297998971 1981029) (P10k.take 173) = wem 297998971 298000002 299980000 := by
  decide +kernel

theorem bnd_164 : MinGBBound 298000002 299980000 1031 :=
  bound_of_wcheck2 (by norm_num) (by norm_num [B2]) (by norm_num) (by decide) (take_le 173 1031 (by decide)) chk_164

theorem lr_164 : (19 + 512603/1000000 : ℝ) ≤ Real.log ((298000002 : ℕ) : ℝ) := by
  have h := le_log_of (x := ((298000002 : ℕ) : ℝ)) 19 (f := (512603/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem ls_164 : (2 + 971059/1000000 : ℝ) ≤ Real.log (19 + 512603/1000000 : ℝ) := by
  have h := le_log_of (x := (19 + 512603/1000000 : ℝ)) 2 (f := (971059/1000000 : ℝ)) (by norm_num) (by norm_num)
    (by simp only [expUp, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]; norm_num)
  push_cast at h ⊢; linarith

theorem r1_164 : ∀ n, Even n → 298000002 ≤ n → n ≤ 299980000 → Ratio 1.603 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_164 ls_164 (by norm_num) (by norm_num) bnd_164

theorem r2_164 : ∀ n, Even n → 298000002 ≤ n → n ≤ 299980000 → Ratio 1.25 n :=
  ratio_of_bound (by norm_num) (by norm_num) lr_164 ls_164 (by norm_num) (by norm_num) bnd_164

end LeanLab.GvLtR1989
