import LeanLab.ExceptionalSet.Decomp371a

/-!
The upper endpoint in the literal floor window for P0082 Lemma7.
The paper's major arc formula is stated for m at most X on page 358.
A shift by one can exceed X at the single index N. Count it separately.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 pages 358 and 362, range of the even integer in Lemma7.
Every interior window index has both adjacent integers below X. -/
theorem adjacent_le_X (γ : ℝ) (hγ : 1 < γ) (N n : ℕ) (hN : 16 ≤ N)
    (hn : n ∈ window γ N) (hnN : n < N) (j : ℤ) (hj : j ≤ 1) :
    (nu γ n + j : ℝ) ≤ F γ N := by
  have hi := mem_Ioc.mp (Decomp371a.window_subset_Ioc γ hγ N hN hn)
  have hn8 : 8 ≤ n := by omega
  have hstep : (1 : ℝ) ≤ (N : ℝ) - n := by
    have hcast : (n : ℝ) + 1 ≤ N := by exact_mod_cast (show n + 1 ≤ N by omega)
    linarith
  have hg := Decomp371a.F_growth γ n N hγ (by exact_mod_cast hn8)
    (by exact_mod_cast hnN.le)
  have hmul := mul_le_mul_of_nonneg_left hstep (show 0 ≤ γ by linarith)
  have hfloor : (nu γ n : ℝ) ≤ F γ n := Int.floor_le _
  have hjR : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  linarith

/-- P0082 page 364, absorbing one endpoint into the exceptional count.
For kappa at most one and N at least eight, N E to minus one twelfth is at least one. -/
theorem one_le_count_scale (γ κ : ℝ) (hγ : 1 < γ) (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (N : ℕ) (hN : 8 ≤ N) :
    1 ≤ (N : ℝ) * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
    have h := Real.log_two_gt_d9
    have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hL : 1 ≤ Real.log (N : ℝ) :=
    hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have hp : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log N := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show 3 - 2 * γ ≤ 1 by linarith)
  have hp0 : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  have hk : κ / 12 * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log N := by
    have h := mul_le_mul_of_nonneg_right (show κ / 12 ≤ 1 by linarith) hp0
    linarith
  rw [calE, ← Real.exp_mul, ← Real.exp_log hN0, ← Real.exp_add]
  apply Real.one_le_exp
  simp only [Real.log_exp]
  nlinarith

end LeanLab.ExceptionalSet.Supply465
