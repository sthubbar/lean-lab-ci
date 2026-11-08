import LeanLab.ExceptionalSet.Growth465

/-!
Scalar absorption for P0082 page360 Lemma5.
The finite error uses P equal to X to six delta and the paper's E scale.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page360 Lemma5. A cubic logarithmic loss is eventually bounded
by the square root of E, even though P is a power of X. -/
theorem logP_cube_le_calE_half (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + Real.log (F γ N ^ (6 * δ))) ^ 3 ≤ calE γ κ N ^ (1 / 2 : ℝ) := by
  let a := 3 - 2 * γ
  let b := κ / 2
  let K := (1 + 6 * δ) ^ 3
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hp := ((isLittleO_rpow_exp_pos_mul_atTop ((3 * γ) / a) hb).const_mul_left K).bound
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
  have hpower : (Real.log (N : ℝ) ^ a) ^ ((3 * γ) / a) = Real.log (N : ℝ) ^ (3 * γ) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    field_simp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hpower,
    abs_of_pos (mul_pos hK (Real.rpow_pos_of_pos hL0 _)),
    abs_of_pos (Real.exp_pos _), one_mul] at he
  have hX : 0 < F γ N := Real.exp_pos _
  have hlogP : Real.log (F γ N ^ (6 * δ)) = 6 * δ * Real.log (N : ℝ) ^ γ := by
    rw [Real.log_rpow hX, F, Real.log_exp]
  have hpow1 : 1 ≤ Real.log (N : ℝ) ^ γ := Real.one_le_rpow hL (by linarith)
  have hbase : 1 + Real.log (F γ N ^ (6 * δ)) ≤ (1 + 6 * δ) * Real.log (N : ℝ) ^ γ := by
    rw [hlogP]
    nlinarith
  have hbase0 : 0 ≤ 1 + Real.log (F γ N ^ (6 * δ)) := by rw [hlogP]; positivity
  have hcubed := pow_le_pow_left₀ hbase0 hbase 3
  have hnormal : ((1 + 6 * δ) * Real.log (N : ℝ) ^ γ) ^ 3 = K * Real.log (N : ℝ) ^ (3 * γ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
    dsimp [K]
    congr 2
    ring
  rw [hnormal] at hcubed
  have hE : calE γ κ N ^ (1 / 2 : ℝ) = Real.exp (b * Real.log (N : ℝ) ^ a) := by
    rw [calE, ← Real.exp_mul]
    congr 1
    dsimp [a, b]
    ring
  rw [hE]
  exact hcubed.trans he

/-- P0082 page360 Lemma5. The inverse square root of P is eventually
at most inverse E because gamma exceeds three minus twice gamma. -/
theorem P_inverse_sqrt_le_inv_E (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) ≤ 1 / calE γ κ N := by
  let a := 3 - 2 * γ
  have hexponent : 0 < γ - a := by dsimp [a]; linarith
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (γ - a)) atTop atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (κ / (3 * δ)))
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLa : 0 < Real.log (N : ℝ) ^ a := Real.rpow_pos_of_pos hL0 _
  have he := hN₀ N ((le_max_right _ _).trans hN)
  rw [Real.rpow_sub hL0] at he
  have hm := (le_div_iff₀ hLa).mp he
  have hlog : κ * Real.log (N : ℝ) ^ a ≤ 3 * δ * Real.log (N : ℝ) ^ γ := by
    have ht := mul_le_mul_of_nonneg_left hm (show 0 ≤ 3 * δ by positivity)
    have hid : (3 * δ) * (κ / (3 * δ) * Real.log (N : ℝ) ^ a) = κ * Real.log (N : ℝ) ^ a := by field_simp
    rw [hid] at ht
    exact ht
  have hX : 0 < F γ N := Real.exp_pos _
  rw [← Real.rpow_mul hX.le]
  rw [F, ← Real.exp_mul, calE]
  simp only [one_div]
  rw [← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  dsimp [a] at hlog
  nlinarith

/-- P0082 page360 Lemma5. The full elementary scalar factor in the finite
Gamma1 average is at most twice E to minus one half for large N. -/
theorem gammaOne_parameters (γ δ κ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + Real.log (F γ N ^ (6 * δ))) ^ 3 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N) ≤
          2 * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨Na, ha⟩ := logP_cube_le_calE_half γ δ κ h1 h2 hδ hκ
  obtain ⟨Nb, hb⟩ := P_inverse_sqrt_le_inv_E γ δ κ h1 h2 hδ hκ
  refine ⟨max Na Nb, fun N hN => ?_⟩
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hX : 0 < F γ N := Real.exp_pos _
  have hleft := ha N ((le_max_left _ _).trans hN)
  have hright := hb N ((le_max_right _ _).trans hN)
  have hsum : (F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N ≤
      2 / calE γ κ N := by
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

end LeanLab.ExceptionalSet.Supply465
