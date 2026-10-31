import LeanLab.PNTSieve.BrunTitchmarshAP

/-!
# Brun-Titchmarsh in arithmetic progressions, the classical form

Lab proof, unit U-5310, CLOUD 20261019T0814Z-cloud20. AI wrote the Lean code. Known mathematics.

`brunTitchmarsh_classical`: there is `X₀` such that for every `q ≥ 1`, every `a` and every real
`x` with `x/q ≥ X₀`, `π(x; q, a) = #{p ≤ x : p ≡ a mod q} ≤ 3x/(φ(q) log(x/q))`.
From `brunTitchmarsh_ap` on `[1, x]` with `z = (x/q)^{3/4}`.
-/

open Finset Real Filter

noncomputable section
namespace LeanLab.PNTSieve.BrunTitchmarshAP

theorem brunTitchmarsh_classical : ∃ X0 : ℝ, 1 < X0 ∧ ∀ (q a : ℕ), 0 < q → ∀ x : ℝ,
    X0 ≤ x / q →
    (((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℝ) ≤
      3 * x / (q.totient * Real.log (x / q)) := by
  have hev : ∀ᶠ u in atTop, 96 * Real.log u ^ (4 : ℝ) ≤ u ^ ((1 : ℝ) / 4) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (show (0 : ℝ) < 1 / 4 by norm_num)).bound
      (show (0 : ℝ) < 1 / 96 by norm_num)
    filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ u by linarith) ((1 : ℝ) / 4))] at hu
    have := le_abs_self (Real.log u ^ (4 : ℝ))
    linarith
  obtain ⟨X1, hX1⟩ := eventually_atTop.mp
    (hev.and ((Real.tendsto_log_atTop.eventually_ge_atTop 4).and (eventually_ge_atTop (2 : ℝ))))
  refine ⟨max X1 2, by have := le_max_right X1 2; linarith, fun q a hq x hx => ?_⟩
  set u := x / q with hu
  obtain ⟨hpow, hL4, hu2⟩ := hX1 u ((le_max_left _ _).trans hx)
  set L := Real.log u with hL
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hu0 : 0 < u := by linarith
  have hxu : x = u * q := by rw [hu]; field_simp
  have hx2 : 2 ≤ x := by rw [hxu]; nlinarith
  have hL0 : 0 < L := by linarith
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set z : ℝ := u ^ ((3 : ℝ) / 4) with hz
  have hz1 : 1 < z := Real.one_lt_rpow (by linarith) (by norm_num)
  have hz0 : 0 < z := by linarith
  have hlz : Real.log z = 3 / 4 * L := by rw [hz, Real.log_rpow hu0]
  have hbt := brunTitchmarsh_ap 1 (x - 1) z q a one_pos (by linarith) hz1 hq
  have hA : ⌈(1 : ℝ)⌉₊ = 1 := Nat.ceil_one
  have hB : ⌊(1 : ℝ) + (x - 1)⌋₊ = ⌊x⌋₊ := by congr 1; ring
  rw [hA, hB, hlz] at hbt
  refine hbt.trans ?_
  -- main term
  have hmain : 2 * (x - 1) / (q.totient * (3 / 4 * L)) ≤ 8 / 3 * x / (q.totient * L) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : 2 * (x - 1) * (q.totient * L) ≤ 2 * x * (q.totient * L) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_pos hφ hL0]
  -- error term
  have herr : 4 * z * (1 + 3 / 4 * L) ^ 3 ≤ 1 / 3 * x / (q.totient * L) := by
    have h1 : (1 + 3 / 4 * L) ^ 3 ≤ 8 * L ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (1 + 3 / 4 * L) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = 8 * L ^ 3 := by ring
    have h4 : L ^ (4 : ℝ) = L ^ (3 : ℝ) * L := by
      rw [show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add hL0, Real.rpow_one]
    have hzu : z * u ^ ((1 : ℝ) / 4) = u := by
      rw [hz, ← Real.rpow_add hu0]; norm_num
    have hux : u ≤ x / q.totient := by
      rw [hu]; exact div_le_div_of_nonneg_left (by linarith) hφ hφq
    have hL3 : 0 ≤ L ^ (3 : ℝ) := Real.rpow_nonneg hL0.le _
    -- 12 z L^4 ≤ u
    have key : 4 * z * (8 * L ^ (3 : ℝ)) * L * 3 ≤ u := by
      calc 4 * z * (8 * L ^ (3 : ℝ)) * L * 3 = z * (96 * L ^ (4 : ℝ)) := by rw [h4]; ring
        _ ≤ z * u ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hpow hz0.le
        _ = u := hzu
    rw [le_div_iff₀ (by positivity)]
    calc 4 * z * (1 + 3 / 4 * L) ^ 3 * (q.totient * L)
        ≤ 4 * z * (8 * L ^ (3 : ℝ)) * (q.totient * L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4 * z * (8 * L ^ (3 : ℝ)) * L * 3) * q.totient / 3 := by ring
      _ ≤ u * q.totient / 3 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right key hφ.le
      _ ≤ x / q.totient * q.totient / 3 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hux hφ.le
      _ = 1 / 3 * x := by field_simp
  calc 2 * (x - 1) / (q.totient * (3 / 4 * L)) + 4 * z * (1 + 3 / 4 * L) ^ 3
      ≤ 8 / 3 * x / (q.totient * L) + 1 / 3 * x / (q.totient * L) := add_le_add hmain herr
    _ = 3 * x / (q.totient * L) := by ring

end LeanLab.PNTSieve.BrunTitchmarshAP
