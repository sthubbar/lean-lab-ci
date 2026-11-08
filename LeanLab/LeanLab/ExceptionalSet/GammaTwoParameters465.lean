import LeanLab.ExceptionalSet.GammaParameters465

/-!
Logarithmic absorption for P0082 pages361 and362, displays18 and19.
The fourth power covers the weaker elementary logarithmic totient envelope.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 pages361 and362, logarithmic loss for the Gamma2 average.
The fourth power of one plus log X is eventually at most square root E. -/
theorem logX_four_le_calE_half (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + Real.log (F γ N)) ^ 4 ≤ calE γ κ N ^ (1 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := logP_cube_le_calE_half γ (1 / 6) (κ / 2) h1 h2 (by norm_num) (by positivity)
  refine ⟨max 8 N₀, fun N hN => ?_⟩
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hN
  have hF : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hH : 1 ≤ 1 + Real.log (F γ N) := by have := Real.log_nonneg hF; linarith
  have hp := hN₀ N ((le_max_right _ _).trans hN)
  norm_num at hp
  have hs := pow_le_pow_left₀ (pow_nonneg (by linarith : 0 ≤ 1 + Real.log (F γ N)) 3) hp 2
  have hid : (calE γ (κ / 2) N ^ (1 / 2 : ℝ)) ^ 2 = calE γ κ N ^ (1 / 2 : ℝ) := by
    have hB : 0 ≤ calE γ (κ / 2) N := (Real.exp_pos _).le
    rw [← Real.rpow_mul_natCast hB]
    norm_num
    rw [calE, calE, ← Real.exp_mul]
    congr 1
    ring
  calc
    _ ≤ (1 + Real.log (F γ N)) ^ 6 := pow_le_pow_right₀ hH (by norm_num)
    _ = ((1 + Real.log (F γ N)) ^ 3) ^ 2 := by ring
    _ ≤ (calE γ (κ / 2) N ^ (1 / 2 : ℝ)) ^ 2 := hs
    _ = _ := hid

/-- P0082 page361 display18, the two elementary near tail factors with
four logarithmic powers are eventually at most twice inverse square root E. -/
theorem gammaTwo_near_parameters (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + Real.log (F γ N)) ^ 4 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N) ≤
          2 * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Na, ha⟩ := logX_four_le_calE_half γ κ h1 h2 hκ
  obtain ⟨Nb, hb⟩ := P_inverse_sqrt_le_inv_E γ δ κ h1 h2 hδ hκ
  refine ⟨max Na Nb, fun N hN => ?_⟩
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hX : 0 < F γ N := Real.exp_pos _
  have hleft := ha N ((le_max_left _ _).trans hN)
  have hright := hb N ((le_max_right _ _).trans hN)
  have hsum : (F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N ≤ 2 / calE γ κ N := by
    rw [show 2 / calE γ κ N = 1 / calE γ κ N + 1 / calE γ κ N by ring]
    linarith
  calc
    _ ≤ calE γ κ N ^ (1 / 2 : ℝ) * (2 / calE γ κ N) :=
      mul_le_mul hleft hsum (by positivity) (Real.rpow_pos_of_pos hE _).le
    _ = _ := by
      rw [show calE γ κ N ^ (1 / 2 : ℝ) * (2 / calE γ κ N) =
        2 * (calE γ κ N ^ (1 / 2 : ℝ) / calE γ κ N) by ring,
        ← Real.rpow_sub_one hE.ne']
      norm_num

/-- P0082 page362 display19, a fixed negative power of X with one
logarithmic factor is eventually below inverse square root E. -/
theorem gammaTwo_far_parameters (γ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + Real.log (F γ N)) * F γ N ^ (-(1 / 8 : ℝ)) ≤
        calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Na, ha⟩ := logX_four_le_calE_half γ κ h1 h2 hκ
  obtain ⟨Nb, hb⟩ := P_inverse_sqrt_le_inv_E γ (1 / 24) κ h1 h2 (by norm_num) hκ
  refine ⟨max 8 (max Na Nb), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hF0 : 0 < F γ N := Real.exp_pos _
  have hF : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hH : 1 ≤ 1 + Real.log (F γ N) := by have := Real.log_nonneg hF; linarith
  have hH4 : 1 + Real.log (F γ N) ≤ (1 + Real.log (F γ N)) ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hH (by norm_num : 1 ≤ 4)
  have hleft := hH4.trans (ha N hNa)
  have hright := hb N hNb
  rw [← Real.rpow_mul hF0.le] at hright
  norm_num at hright
  have hright' : F γ N ^ (-(1 / 8 : ℝ)) ≤ 1 / calE γ κ N := by simpa only [one_div] using hright
  have hE : 0 < calE γ κ N := Real.exp_pos _
  calc
    _ ≤ calE γ κ N ^ (1 / 2 : ℝ) * (1 / calE γ κ N) :=
      mul_le_mul hleft hright' (Real.rpow_pos_of_pos hF0 _).le (Real.rpow_pos_of_pos hE _).le
    _ = _ := by rw [mul_one_div, ← Real.rpow_sub_one hE.ne']; norm_num

end LeanLab.ExceptionalSet.Supply465
