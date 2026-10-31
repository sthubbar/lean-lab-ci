import Mathlib

/-!
# A six digit lower bound for Euler's constant: `0.57721 < γ₀`

Session PC 20261021T0003Z-5661, unit U-1299, paper P0032 Riesel-Vaughan 1983, track T1.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here bears on it directly.

Known mathematics, no cited input. The trapezoid bound
`log (1 + 1/n) ≤ 2/(2n+1) + 1/(6(2n+1)n(n+1)) ≤ (1/n + 1/(n+1))/2`, from Mathlib's series
`hasSum_log_one_add_inv` compared with a geometric series, makes the Euler-Maclaurin corrected
sequence `H_n − log n − 1/(2n)` increasing; it tends to `γ₀`, so `γ₀ ≥ H_128 − 7 log 2 − 1/256`,
which is `> 0.5772104`. True value `0.5772156649`.
-/

namespace LeanLab.RieselVaughan1983

open Real Filter Topology

lemma log_one_add_inv_le (n : ℕ) (hn : 0 < n) :
    Real.log (1 + (n : ℝ)⁻¹) ≤
      2 / (2 * n + 1) + 1 / (6 * (2 * n + 1) * n * (n + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.hasSum_log_one_add_inv (a := (n : ℝ)) (by linarith)
  set z : ℝ := 1 / (2 * n + 1) with hz
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have hz2 : z ^ 2 < 1 := by nlinarith
  rw [← hasSum_nat_add_iff' 1] at hs
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_add,
    pow_one, div_one, mul_one] at hs
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg z) hz2).mul_left (2 / 3 * z ^ 3)
  have hle := hasSum_le (fun k => ?_) hs hg
  · have hz2' : (1 - z ^ 2) = 4 * n * (n + 1) / (2 * n + 1) ^ 2 := by
      rw [hz]; field_simp; ring
    have hfin : 2 / 3 * z ^ 3 * (1 - z ^ 2)⁻¹ = 1 / (6 * (2 * n + 1) * n * (n + 1)) := by
      rw [hz2', hz]; field_simp; ring
    rw [hfin] at hle
    have : 2 * z = 2 / (2 * n + 1) := by rw [hz]; ring
    linarith
  · show 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ) + 1)) * z ^ (2 * (k + 1) + 1) ≤ 2 / 3 * z ^ 3 * (z ^ 2) ^ k
    have hp : z ^ (2 * (k + 1) + 1) = z ^ 3 * (z ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have hk : (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast
      nlinarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have hzz : 0 ≤ z ^ 3 * (z ^ 2) ^ k := by positivity
    rw [hp]; nlinarith

/-- The Euler-Maclaurin corrected sequence `H_n − log n − 1/(2n)` at `n = k + 1`. -/
noncomputable def emSeq (k : ℕ) : ℝ :=
  (harmonic (k + 1) : ℝ) - Real.log ((k : ℝ) + 1) - 1 / (2 * ((k : ℝ) + 1))

lemma emSeq_le_succ (k : ℕ) : emSeq k ≤ emSeq (k + 1) := by
  have hL := log_one_add_inv_le (k + 1) (Nat.succ_pos k)
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hn
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast Nat.succ_pos k
  have hlog : Real.log (n + 1) = Real.log n + Real.log (1 + n⁻¹) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hH : (harmonic (k + 2) : ℝ) = harmonic (k + 1) + 1 / (n + 1) := by
    rw [harmonic_succ]; push_cast; rw [hn]; push_cast; ring
  unfold emSeq
  have e1 : ((k : ℝ) + 1) = n := by rw [hn]; push_cast; ring
  have e2 : (((k + 1 : ℕ) : ℝ) + 1) = n + 1 := by rw [hn]
  rw [e1, e2, hH, hlog]
  -- `1/(n+1) − 1/(2(n+1)) + 1/(2n) ≥ 2/(2n+1) + 1/(6(2n+1)n(n+1))`
  have key : 2 / (2 * n + 1) + 1 / (6 * (2 * n + 1) * n * (n + 1)) ≤
      1 / (n + 1) - 1 / (2 * (n + 1)) + 1 / (2 * n) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity)
      (by positivity), div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (by positivity : (0:ℝ) < n) (by positivity : (0:ℝ) < n + 1),
      pow_pos (by positivity : (0:ℝ) < n) 3, pow_pos (by positivity : (0:ℝ) < n) 4,
      pow_pos (by positivity : (0:ℝ) < n) 5, pow_pos (by positivity : (0:ℝ) < n) 6]
  linarith

lemma tendsto_emSeq : Tendsto emSeq atTop (𝓝 eulerMascheroniConstant) := by
  have h1 := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have h3 := h1.sub h2
  rw [zero_div, sub_zero] at h3
  refine h3.congr (fun k => ?_)
  simp only [Function.comp, emSeq]; push_cast; congr 1; rw [div_div, mul_comm]

lemma emSeq_le_gamma (k : ℕ) : emSeq k ≤ eulerMascheroniConstant :=
  (monotone_nat_of_le_succ emSeq_le_succ).ge_of_tendsto tendsto_emSeq k

lemma log128 : Real.log 128 = 7 * Real.log 2 := by
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num

lemma harmonic128_gt : (5433147 / 1000000 : ℚ) < harmonic 128 := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

/-- `0.57721 < γ₀`, PROVED unconditional. -/
theorem gamma_gt_sharp : (57721 / 100000 : ℝ) < eulerMascheroniConstant := by
  have h := emSeq_le_gamma 127
  have hl := Real.log_two_lt_d9
  have hv : ((5433147 / 1000000 : ℚ) : ℝ) < ((harmonic 128 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr harmonic128_gt
  unfold emSeq at h
  have e : ((127 : ℕ) : ℝ) + 1 = 128 := by norm_num
  rw [e, log128] at h
  push_cast at hv h
  linarith

end LeanLab.RieselVaughan1983
