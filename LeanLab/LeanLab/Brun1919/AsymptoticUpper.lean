/-
AI-written Lean code, Codex task05, 2026-10-22.
General power-level estimates for the existing Selberg twin-prime sieve.
These are lab consequences of Sieve.twinCount_le and Mathlib logarithmic limits.
No asymptotic constant is attributed to the original 1919 scan.
-/
import LeanLab.Brun1919.SharperTaylor

open Filter
open scoped Topology

noncomputable section
namespace LeanLab.Brun1919

/-- A normalized remainder bound for any nonnegative power-level exponent. -/
lemma power_sieve_error_ratio_le (x a : ℝ) (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x)
    (ha : 0 ≤ a) :
    (x ^ a * (1 + Real.log (x ^ a)) ^ 6 + (x ^ a + 1)) * Real.log x ^ 2 / x ≤
      (3 * (1 + a) ^ 6) * (Real.log x ^ 8 / x ^ (1 - a)) := by
  have hx0 : 0 < x := by linarith
  have hxa0 : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hx0 a).le
  have hxa1 : 1 ≤ x ^ a := Real.one_le_rpow hx ha
  have hl0 : 0 ≤ Real.log x := by linarith
  have hb : 1 + Real.log (x ^ a) ≤ (1 + a) * Real.log x := by
    rw [Real.log_rpow hx0]
    nlinarith
  have hb0 : 0 ≤ 1 + Real.log (x ^ a) := by
    rw [Real.log_rpow hx0]
    positivity
  have hpow : (1 + Real.log (x ^ a)) ^ 6 ≤ (1 + a) ^ 6 * Real.log x ^ 6 := by
    calc
      _ ≤ ((1 + a) * Real.log x) ^ 6 := by gcongr
      _ = _ := mul_pow _ _ _
  have ha6 : 1 ≤ (1 + a) ^ 6 := one_le_pow₀ (by linarith)
  have hl6 : 1 ≤ Real.log x ^ 6 := one_le_pow₀ hlog
  have hA : 1 ≤ (1 + a) ^ 6 * Real.log x ^ 6 := by
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ _ := by gcongr
  have he : x ^ a * (1 + Real.log (x ^ a)) ^ 6 + (x ^ a + 1) ≤
      3 * x ^ a * ((1 + a) ^ 6 * Real.log x ^ 6) := by
    have h1 := mul_le_mul_of_nonneg_left hpow hxa0
    have h2 := mul_le_mul_of_nonneg_left hA hxa0
    nlinarith
  have hprod : x ^ a * x ^ (1 - a) = x := by
    rw [← Real.rpow_add hx0, show a + (1 - a) = 1 by ring, Real.rpow_one]
  have hquot : x ^ a / x = 1 / x ^ (1 - a) := by
    apply (div_eq_div_iff hx0.ne' (Real.rpow_pos_of_pos hx0 _).ne').mpr
    simpa using hprod
  calc
    _ ≤ (3 * x ^ a * ((1 + a) ^ 6 * Real.log x ^ 6)) * Real.log x ^ 2 / x := by gcongr
    _ = (3 * (1 + a) ^ 6) * (Real.log x ^ 8 * (x ^ a / x)) := by ring
    _ = _ := by rw [hquot]; ring

/-- The normalized remainder majorant tends to zero for every exponent below one. -/
lemma power_log_error_majorant_tendsto (a : ℝ) (ha : a < 1) :
    Tendsto (fun x : ℝ => (3 * (1 + a) ^ 6) * (Real.log x ^ 8 / x ^ (1 - a)))
      atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (8 : ℝ)
    (by linarith : 0 < 1 - a)).tendsto_div_nhds_zero
  have hn : Tendsto (fun x : ℝ => Real.log x ^ 8 / x ^ (1 - a)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using h
  simpa using tendsto_const_nhds.mul hn

/-- Any fixed power level between zero and one gives an eventual explicit main coefficient. -/
theorem twinCount_eventually_le_power (a ε : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (twinCount N : ℝ) ≤ (48 / a ^ 2 + ε) * N / Real.log N ^ 2 := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := (power_log_error_majorant_tendsto a ha1).comp hcast
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (3 * (1 + a) ^ 6) * (Real.log (N : ℝ) ^ 8 / (N : ℝ) ^ (1 - a)) < ε :=
    (tendsto_order.mp hlim).2 ε hε
  have hlogev : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  filter_upwards [hsmall, hlogev, eventually_ge_atTop (3 : ℕ)] with N hsm hlog hN
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hN0 : 0 < (N : ℝ) := by linarith
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  let E := (N : ℝ) ^ a * (1 + Real.log ((N : ℝ) ^ a)) ^ 6 + ((N : ℝ) ^ a + 1)
  have hr := power_sieve_error_ratio_le (N : ℝ) a hN1.le hlog ha0.le
  have hEnorm : E * Real.log N ^ 2 / N ≤ ε := hr.trans hsm.le
  have hE : E ≤ ε * N / Real.log N ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlog0)).mpr
    exact (div_le_iff₀ hN0).mp hEnorm
  have hz : 1 < (N : ℝ) ^ a := Real.one_lt_rpow hN1 ha0
  have h := twinCount_le N hz
  have hm : 48 * (N : ℝ) / Real.log ((N : ℝ) ^ a) ^ 2 =
      (48 / a ^ 2) * N / Real.log N ^ 2 := by
    rw [Real.log_rpow hN0]
    field_simp [ha0.ne', hlog0.ne']
    <;> ring
  rw [hm] at h
  have hbound : (twinCount N : ℝ) ≤ (48 / a ^ 2) * N / Real.log N ^ 2 + E := by
    dsimp [E]
    linarith
  calc
    (twinCount N : ℝ) ≤ (48 / a ^ 2) * N / Real.log N ^ 2 + E := hbound
    _ ≤ (48 / a ^ 2) * N / Real.log N ^ 2 + ε * N / Real.log N ^ 2 := by linarith
    _ = (48 / a ^ 2 + ε) * N / Real.log N ^ 2 := by ring

/-- Every coefficient strictly above 48 bounds twin counts for sufficiently large N. -/
theorem twinCount_eventually_le_constant (C : ℝ) (hC : 48 < C) :
    ∀ᶠ N : ℕ in atTop, (twinCount N : ℝ) ≤ C * N / Real.log N ^ 2 := by
  let a := Real.sqrt (96 / (C + 48))
  have hsum : 0 < C + 48 := by linarith
  have hratio : 0 < (96 : ℝ) / (C + 48) := by positivity
  have ha0 : 0 < a := Real.sqrt_pos.mpr hratio
  have hasq : a ^ 2 = 96 / (C + 48) := Real.sq_sqrt hratio.le
  have hasq_lt : a ^ 2 < 1 := by
    rw [hasq]
    exact (div_lt_one hsum).mpr (by linarith)
  have ha1 : a < 1 := by nlinarith
  have hmain : 48 / a ^ 2 = (C + 48) / 2 := by
    rw [hasq]
    field_simp
    <;> ring
  have hε : 0 < (C - 48) / 2 := by linarith
  have h := twinCount_eventually_le_power a ((C - 48) / 2) ha0 ha1 hε
  have hc : 48 / a ^ 2 + (C - 48) / 2 = C := by rw [hmain]; ring
  simpa only [hc] using h

/-- The original pure-sieve upper-bound shape, derived here from the stronger modern bound. -/
theorem pure_brun_shape_eventually :
    ∀ᶠ N : ℕ in atTop, (twinCount N : ℝ) ≤
      896 * N * (Real.log (Real.log N) / Real.log N) ^ 2 := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hll : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (Real.log (N : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hcast)).eventually_ge_atTop 1
  filter_upwards [hll, eventually_ge_atTop (3 : ℕ)] with N hlog hN
  have hs : 1 ≤ Real.log (Real.log (N : ℝ)) ^ 2 := one_le_pow₀ hlog
  have hn : 0 ≤ 896 * (N : ℝ) / Real.log N ^ 2 := by positivity
  calc
    (twinCount N : ℝ) ≤ 896 * N / Real.log N ^ 2 := twinCount_le_896 N hN
    _ ≤ (896 * N / Real.log N ^ 2) * Real.log (Real.log N) ^ 2 := by
      nlinarith [mul_nonneg hn (sub_nonneg.mpr hs)]
    _ = 896 * N * (Real.log (Real.log N) / Real.log N) ^ 2 := by rw [div_pow]; ring

#print axioms pure_brun_shape_eventually

#print axioms twinCount_eventually_le_constant

#print axioms twinCount_eventually_le_power

#print axioms power_log_error_majorant_tendsto

#print axioms power_sieve_error_ratio_le

end LeanLab.Brun1919
