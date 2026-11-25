import LeanLab.ExceptionalSet.State1539Data264

/-!
Feed 1122, the LEAF `leaf_near_zero_conductor_power` of `Feed1122_near_zero_even_index.lean`,
P0082 page 364 last lines, the step from display 10 to `X calE^(-1/10)`.

For `1 ≤ r ≤ calE^(1/7)` one has `√r (log (r + 2))^2 ≤ calE^(1/10)` once `N` is large, since
`calE = exp (κ (log N)^(3 - 2γ))` tends to infinity for `γ < 3/2`.  With `v = calE^(1/140)` we
have `r ≤ v^20`, so `√r ≤ v^10` and `log (r + 2) ≤ log (v^21) = 21 log v ≤ 42 √v`, whence
`√r (log (r + 2))^2 ≤ 1764 v^11 ≤ v^14 = calE^(1/10)` as soon as `v ≥ 40`.

This file does not import the leaf file, so the leaf file may import it.
AI wrote the Lean code, CLOUD S134.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Filter
open LeanLab.ExceptionalSet.U1539 (calE)

/-- The real inequality behind P0082 page 364 last lines: if `v = E^(1/140) ≥ 40` and
`1 ≤ r ≤ E^(1/7)` then `√r (log (r + 2))^2 ≤ E^(1/10)`. -/
theorem conductor_power_real_s134 (E : ℝ) (hE : 0 < E) (hv : 40 ≤ E ^ (1 / 140 : ℝ))
    (r : ℝ) (hr : 1 ≤ r) (hrE : r ≤ E ^ (1 / 7 : ℝ)) :
    Real.sqrt r * Real.log (r + 2) ^ 2 ≤ E ^ (1 / 10 : ℝ) := by
  set v := E ^ (1 / 140 : ℝ) with hvdef
  have hv0 : 0 < v := by positivity
  have hpow : ∀ k : ℕ, E ^ ((k : ℝ) / 140) = v ^ k := by
    intro k
    rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have h7 : E ^ (1 / 7 : ℝ) = v ^ 20 := by
    rw [← hpow 20]; norm_num
  have h10 : E ^ (1 / 10 : ℝ) = v ^ 14 := by
    rw [← hpow 14]; norm_num
  rw [h7] at hrE
  rw [h10]
  -- `√r ≤ v^10`
  have hsq : Real.sqrt r ≤ v ^ 10 := by
    have : Real.sqrt (v ^ 20) = v ^ 10 := by
      rw [show v ^ 20 = (v ^ 10) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [← this]
    exact Real.sqrt_le_sqrt hrE
  -- `log (r + 2) ≤ 21 log v`
  have hv1 : 1 ≤ v := by linarith
  have h21 : r + 2 ≤ v ^ 21 := by
    have : v ^ 20 * 40 ≤ v ^ 21 := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hv (by positivity)
    have h1 : (1 : ℝ) ≤ v ^ 20 := one_le_pow₀ hv1
    nlinarith
  have hlog1 : Real.log (r + 2) ≤ 21 * Real.log v := by
    have := Real.log_le_log (by linarith) h21
    rwa [Real.log_pow] at this
  -- `log v ≤ 2 √v`
  have hlogv : Real.log v ≤ 2 * Real.sqrt v := by
    have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hv0)
    rw [Real.log_sqrt hv0.le] at hs
    linarith
  have hL0 : 0 ≤ Real.log (r + 2) := Real.log_nonneg (by linarith)
  have hL : Real.log (r + 2) ≤ 42 * Real.sqrt v := by linarith
  have hL2 : Real.log (r + 2) ^ 2 ≤ 1764 * v := by
    have := pow_le_pow_left₀ hL0 hL 2
    have hsv : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
    nlinarith
  have hv3 : 1764 ≤ v ^ 3 := by
    have : (40 : ℝ) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ (by norm_num) hv 3
    nlinarith
  calc Real.sqrt r * Real.log (r + 2) ^ 2 ≤ v ^ 10 * (1764 * v) :=
        mul_le_mul hsq hL2 (by positivity) (by positivity)
    _ = 1764 * v ^ 11 := by ring
    _ ≤ v ^ 3 * v ^ 11 := mul_le_mul_of_nonneg_right hv3 (by positivity)
    _ = v ^ 14 := by ring

/-- `calE γ κ N` tends to infinity with `N` for `γ < 3/2` and `κ > 0`. -/
theorem calE_tendsto_s134 (γ : ℝ) (h2 : γ < 3 / 2) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
  unfold calE
  have ha : 0 < 3 - 2 * γ := by linarith
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hlog
  exact Real.tendsto_exp_atTop.comp (hp.const_mul_atTop hκ)

/-- Verbatim statement of `leaf_near_zero_conductor_power`, P0082 page 364 last lines. -/
theorem leaf_near_zero_conductor_power_s134 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
      calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ 1 / (Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((calE_tendsto_s134 γ h2 κ hκ).eventually_ge_atTop ((40 : ℝ) ^ (140 : ℕ)))
  refine ⟨N₀, fun N hN r hr hrE => ?_⟩
  have hE := hN₀ N hN
  have hEpos : 0 < calE γ κ N := Real.exp_pos _
  have hv : 40 ≤ calE γ κ N ^ (1 / 140 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hE (by norm_num : (0 : ℝ) ≤ 1 / 140)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    have e : ((140 : ℕ) : ℝ) * (1 / 140) = 1 := by norm_num
    rwa [e, Real.rpow_one] at h
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkey := conductor_power_real_s134 _ hEpos hv (r : ℝ) hr1 hrE
  have hD : 0 < Real.sqrt r * Real.log ((r : ℝ) + 2) ^ 2 := by
    have : 0 < Real.log ((r : ℝ) + 2) := Real.log_pos (by linarith)
    positivity
  rw [Real.rpow_neg hEpos.le, ← one_div]
  exact one_div_le_one_div_of_le hD hkey

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
