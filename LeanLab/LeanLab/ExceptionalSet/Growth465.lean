import LeanLab.ExceptionalSet.State1539Data264

/-!
The logarithmic factor in the second term of P0082 page364 display22.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page364 after display22. The logarithmic conductor factor divided
by E is eventually at most E to minus one twelfth. This is elementary
exponential domination, with the paper's actual E scale. -/
theorem logarithmic_error_absorbed (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + 6 * δ * Real.log (F γ N)) / calE γ κ N ≤
        calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  let a := 3 - 2 * γ
  let b := κ * (11 / 12 : ℝ)
  let K := 1 + 6 * δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hp := ((isLittleO_rpow_exp_pos_mul_atTop (γ / a) hb).const_mul_left K).bound
    (show (0 : ℝ) < 1 by norm_num)
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually hp)
  refine ⟨max 8 N₀, fun N hN => ?_⟩
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hN
  have hL : 1 ≤ Real.log (N : ℝ) := by
    have hlog8 : (1 : ℝ) ≤ Real.log 8 := by
      have h := Real.log_two_gt_d9
      have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      linarith
    exact hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hN8))
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have he := hN₀ N ((le_max_right _ _).trans hN)
  have hpowers : (Real.log (N : ℝ) ^ a) ^ (γ / a) = Real.log (N : ℝ) ^ γ := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hpowers,
    abs_of_pos (mul_pos hK (Real.rpow_pos_of_pos hL0 _)),
    abs_of_pos (Real.exp_pos _), one_mul] at he
  have hpow1 : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hL (by linarith)
  have hmain : 1 + 6 * δ * Real.log (F γ N) ≤ Real.exp (b * Real.log (N : ℝ) ^ a) := by
    rw [F, Real.log_exp]
    dsimp [K] at he
    linarith
  have hE : 0 < calE γ κ N := Real.exp_pos _
  apply (div_le_iff₀ hE).mpr
  have hid : calE γ κ N ^ (-(1 / 12 : ℝ)) * calE γ κ N =
      Real.exp (b * Real.log (N : ℝ) ^ a) := by
    rw [calE, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    dsimp [a, b]
    ring
  rw [hid]
  exact hmain

end LeanLab.ExceptionalSet.Supply465
