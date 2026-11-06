import LeanLab.AlmostPrimeSums.Triple243
import LeanLab.HeathBrownPuchta.Decomp1530b

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Qualitative prime counting upper input for BJS p. 57 equation 186.
The lab already proves the natural endpoint upper prime number theorem in
HeathBrownPuchta.Decomp1530b.pi_upper. This file supplies real quotient endpoints.
No cited Rosser or Dusart bound is assumed.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.PrimeCount243

open Finset Real Filter Topology

/-- Prime counting at a real quotient has the qualitative upper coefficient one.
This is the prime number theorem input for BJS p. 57 equation 186, derived
from the existing proved natural endpoint theorem and an elementary floor comparison. -/
theorem primeCounting_real_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1 + ε) * x / log x := by
  have hnat : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (1 + ε / 2) * n / log n := by
    have hh := LeanLab.HeathBrownPuchta.Decomp1530b.pi_upper (by norm_num : (0 : ℝ) ≤ 0)
      (ε / 2) (by positivity)
    have hset (n : ℕ) : LeanLab.HeathBrownPuchta.Decomp1530b.primesIn n 0 = Nat.primesLE n := by
      rw [Nat.primesLE_eq_filter_Icc_one]
      apply filter_congr
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from (mem_Icc.mp hp).1)
      simp only [LeanLab.HeathBrownPuchta.Decomp1530b.primesIn, zero_mul]
      exact and_iff_left hp0
    filter_upwards [hh] with n hn
    rwa [hset, Nat.primesLE_card_eq_primeCounting] at hn
  have hfloor := (tendsto_nat_floor_atTop :
    Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop).eventually hnat
  have hlog := tendsto_log_atTop.eventually_ge_atTop (2 * (1 + ε) * log 2 / ε)
  filter_upwards [hfloor, hlog, eventually_ge_atTop (4 : ℝ)] with x hπ hthreshold hx4
  have hx : 0 < x := by linarith
  have hxlog : 0 < log x := log_pos (by linarith)
  have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one x
    linarith
  have hflpos : 0 < (⌊x⌋₊ : ℝ) := (div_pos hx (by norm_num)).trans_le hfl
  have hlogfl : 0 < log (⌊x⌋₊ : ℝ) := log_pos (by linarith)
  have hden : 0 < log x - log 2 := sub_pos.mpr (log_lt_log (by norm_num) (by linarith))
  have hloglo : log x - log 2 ≤ log (⌊x⌋₊ : ℝ) := by
    have hh := log_le_log (div_pos hx (by norm_num)) hfl
    rwa [log_div hx.ne' (by norm_num)] at hh
  have hcoef : (1 + ε / 2) / (log x - log 2) ≤ (1 + ε) / log x := by
    rw [div_le_div_iff₀ hden hxlog]
    have hh := (div_le_iff₀ hε).mp hthreshold
    nlinarith
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1 + ε / 2) * (⌊x⌋₊ : ℝ) / log (⌊x⌋₊ : ℝ) := hπ
    _ ≤ (1 + ε / 2) * x / log (⌊x⌋₊ : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogfl.le
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hx.le) (by positivity)
    _ ≤ (1 + ε / 2) * x / (log x - log 2) := by
      exact div_le_div_of_nonneg_left (by positivity) hden hloglo
    _ = x * ((1 + ε / 2) / (log x - log 2)) := by ring
    _ ≤ x * ((1 + ε) / log x) := mul_le_mul_of_nonneg_left hcoef hx.le
    _ = (1 + ε) * x / log x := by ring

/-- The qualitative prime counting estimate is uniform over the actual double
prime sum for T. Every quotient exceeds the second prime and hence the
moving lower cutoff. This supplies the prime counting step of BJS p. 57 equation 186. -/
theorem primeCounting_triple_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ p₁ ∈ LeanLab.AlmostPrimeSums.Decomp243b.middlePrimes N,
      ∀ p₂ ∈ LeanLab.ChenExplicit.D1552.primesIco ((N : ℝ) ^ ((1 : ℝ) / 3))
        (√((N : ℝ) / p₁)),
      (Nat.primeCounting ⌊(N : ℝ) / (p₁ * p₂)⌋₊ : ℝ) ≤
        (1 + ε) * N * (1 / (p₁ : ℝ)) *
          (1 / ((p₂ : ℝ) * log ((N : ℝ) / (p₁ * p₂)))) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (primeCounting_real_upper ε hε)
  have hy : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hy.eventually_ge_atTop X] with N hN
  intro p₁ hp₁ p₂ hp₂
  have hp1 : p₁.Prime := (mem_filter.mp hp₁).2.1
  have hp2 : p₂.Prime := (mem_filter.mp hp₂).2.1
  have hp1R : (0 : ℝ) < p₁ := by exact_mod_cast hp1.pos
  have hp2R : (0 : ℝ) < p₂ := by exact_mod_cast hp2.pos
  have hlow : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ p₂ := (mem_filter.mp hp₂).2.2
  have hupp : (p₂ : ℝ) < √((N : ℝ) / p₁) :=
    Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp₂).1)
  have hsquare : (p₂ : ℝ) ^ 2 < (N : ℝ) / p₁ := (lt_sqrt hp2R.le).mp hupp
  rw [lt_div_iff₀ hp1R] at hsquare
  have hquot : (p₂ : ℝ) < (N : ℝ) / (p₁ * p₂) := by
    apply (lt_div_iff₀ (mul_pos hp1R hp2R)).mpr
    nlinarith only [hsquare]
  have hh := hX ((N : ℝ) / (p₁ * p₂)) (hN.trans (hlow.trans hquot.le))
  convert hh using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev, one_mul] <;> ring

end LeanLab.AlmostPrimeSums.PrimeCount243
