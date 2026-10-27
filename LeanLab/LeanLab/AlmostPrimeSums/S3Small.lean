/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0072 Togashi and Uchiyama 1964, Section 5 p. 67.
An elementary comparison of the S3 bound with the totient scale.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.S3Asymptotic
import LeanLab.HeathBrown1985.Elementary

open Finset Filter Real Asymptotics
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5

namespace LeanLab.AlmostPrimeSums.S3Small

/-- An elementary lower bound on the totient, for the p. 67 error comparison. -/
lemma le_totient_mul_log {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ log (N : ℝ)) :
    (N : ℝ) ≤ (exp 1 * (1 + 1 / log 2)) * N.totient * log N := by
  have hp : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr hN
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hw := LeanLab.HeathBrown1985.card_primeFactors_mul_log_two_le N hN
  have hdiv := LeanLab.HeathBrown1985.div_totient_le N hN
  have hw' : (N.primeFactors.card : ℝ) ≤ log N / log 2 := (le_div_iff₀ h2).mpr hw
  have hlog : 1 + (N.primeFactors.card : ℝ) ≤ (1 + 1 / log 2) * log N := by
    calc
      _ ≤ 1 + log N / log 2 := by linarith
      _ ≤ log N + log N / log 2 := by linarith
      _ = _ := by ring
  have hratio : (N : ℝ) / N.totient ≤ (exp 1 * (1 + 1 / log 2)) * log N := by
    calc
      _ ≤ exp 1 * (1 + N.primeFactors.card) := hdiv
      _ ≤ exp 1 * ((1 + 1 / log 2) * log N) := mul_le_mul_of_nonneg_left hlog (exp_pos _).le
      _ = _ := by ring
  have := (div_le_iff₀ hp).mp hratio
  nlinarith

example : (3 : ℝ) ≤ (exp 1 * (1 + 1 / log 2)) * (3 : ℕ).totient * log 3 := by
  apply le_totient_mul_log (by norm_num)
  have h : exp (1 : ℝ) < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have hh := log_le_log (exp_pos 1) h.le
  simpa only [log_exp, Nat.cast_ofNat] using hh

/-- N to the power 5/6 is negligible against phi of N divided by log squared N. -/
theorem rpow_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      6 * (N : ℝ) ^ (5 / 6 : ℝ) ≤ ε * (N.totient : ℝ) / (log N) ^ 2 := by
  let C : ℝ := exp 1 * (1 + 1 / log 2)
  have hC : 0 < C := by dsimp [C]; have : 0 < log (2 : ℝ) := log_pos (by norm_num); positivity
  have heta : 0 < ε / (6 * C) := by positivity
  have hs : (fun x : ℝ => log x ^ (3 : ℝ)) =o[atTop] (fun x => x ^ (1 / 6 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 3 (by norm_num)
  have hsN := (hs.comp_tendsto tendsto_natCast_atTop_atTop).bound heta
  have hL : ∀ᶠ N : ℕ in atTop, 1 ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsN, hL, eventually_ge_atTop 1] with N hsN hL hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hs' : (log (N : ℝ)) ^ 3 ≤ ε / (6 * C) * (N : ℝ) ^ (1 / 6 : ℝ) := by
    simpa only [Function.comp_apply, rpow_ofNat, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (log (N : ℝ)) ^ 3),
      abs_of_nonneg (rpow_nonneg hN0.le _)] using hsN
  have heq : (N : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) = N := by
    rw [← rpow_add hN0]; norm_num
  have hb : 6 * C * (N : ℝ) ^ (5 / 6 : ℝ) * (log N) ^ 3 ≤ ε * N := by
    have h := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 6 * C * (N : ℝ) ^ (5 / 6 : ℝ))
    calc
      _ ≤ 6 * C * (N : ℝ) ^ (5 / 6 : ℝ) * (ε / (6 * C) * (N : ℝ) ^ (1 / 6 : ℝ)) := h
      _ = ε * N := by field_simp; nlinarith [heq]
  have hphi := le_totient_mul_log hN hL
  change (N : ℝ) ≤ C * N.totient * log N at hphi
  have hmain : 6 * (N : ℝ) ^ (5 / 6 : ℝ) * (log N) ^ 2 ≤ ε * N.totient := by
    apply (mul_le_mul_iff_left₀ (mul_pos hC hL0)).mp
    calc
      (6 * (N : ℝ) ^ (5 / 6 : ℝ) * (log N) ^ 2) * (C * log N)
          = 6 * C * (N : ℝ) ^ (5 / 6 : ℝ) * (log N) ^ 3 := by ring
      _ ≤ ε * N := hb
      _ ≤ ε * (C * N.totient * log N) := mul_le_mul_of_nonneg_left hphi hε.le
      _ = (ε * N.totient) * (C * log N) := by ring
  exact (le_div_iff₀ (sq_pos_of_pos hL0)).mpr hmain

/-- Section 5 p. 67: the S3 error is below every positive totient scale. -/
theorem S3_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((S3set N).card : ℝ) ≤ ε * (N.totient : ℝ) / (log N) ^ 2 := by
  filter_upwards [rpow_eventually_le hε, eventually_ge_atTop 1] with N hN hpos
  exact (S3Asymptotic.S3_card_le_six_rpow hpos).trans hN

/-- Section 5 p. 67: S3 is little o of phi divided by log squared. -/
theorem S3_card_isLittleO :
    (fun N : ℕ => ((S3set N).card : ℝ))
      =o[atTop] (fun N : ℕ => (N.totient : ℝ) / (log N) ^ 2) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [S3_eventually_le hε] with N hN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  simpa only [mul_div_assoc] using hN

/-- Scale the elementary S3 bound by any positive lower normalization. -/
theorem S3_eventually_le_scaled {a ε : ℝ} {M : ℕ → ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hM : ∀ᶠ N : ℕ in atTop, a * (N.totient : ℝ) / (log N) ^ 2 ≤ M N) :
    ∀ᶠ N : ℕ in atTop, ((S3set N).card : ℝ) ≤ ε * M N := by
  filter_upwards [S3_eventually_le (mul_pos hε ha), hM] with N hs hm
  calc
    _ ≤ (ε * a) * (N.totient : ℝ) / (log N) ^ 2 := hs
    _ = ε * (a * (N.totient : ℝ) / (log N) ^ 2) := by ring
    _ ≤ ε * M N := mul_le_mul_of_nonneg_left hm hε.le

example : ∃ N : ℕ, 28 ≤ N ∧
    ((S3set N).card : ℝ) ≤ (N.totient : ℝ) / (log N) ^ 2 := by
  have h := (eventually_ge_atTop (28 : ℕ)).and (S3_eventually_le (ε := 1) (by norm_num))
  simpa only [one_mul] using h.exists

lemma totient_scale_tendsto :
    Tendsto (fun N : ℕ => (N.totient : ℝ) / (log N) ^ 2) atTop atTop := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (5 / 6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 6)).comp tendsto_natCast_atTop_atTop
  have hs := rpow_eventually_le (ε := 1) (by norm_num)
  simp only [one_mul] at hs
  exact tendsto_atTop_mono' atTop hs (Tendsto.const_mul_atTop (by norm_num) hpow)

lemma scaled_size_eventually {a : ℝ} {M : ℕ → ℝ} (ha : 0 < a)
    (hM : ∀ᶠ N : ℕ in atTop, a * (N.totient : ℝ) / (log N) ^ 2 ≤ M N) :
    ∀ᶠ N : ℕ in atTop, 2 < (0.0269 : ℝ) * M N := by
  have ht : Tendsto M atTop atTop :=
    tendsto_atTop_mono' atTop (by
      filter_upwards [hM] with N hn
      simpa only [mul_div_assoc] using hn)
      (Tendsto.const_mul_atTop ha totient_scale_tendsto)
  have h := (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 0.0269) ht).eventually_gt_atTop 2
  exact h

end LeanLab.AlmostPrimeSums.S3Small

#print axioms LeanLab.AlmostPrimeSums.S3Small.le_totient_mul_log

#print axioms LeanLab.AlmostPrimeSums.S3Small.rpow_eventually_le

#print axioms LeanLab.AlmostPrimeSums.S3Small.S3_eventually_le

#print axioms LeanLab.AlmostPrimeSums.S3Small.S3_card_isLittleO

#print axioms LeanLab.AlmostPrimeSums.S3Small.S3_eventually_le_scaled

#print axioms LeanLab.AlmostPrimeSums.S3Small.totient_scale_tendsto

#print axioms LeanLab.AlmostPrimeSums.S3Small.scaled_size_eventually
