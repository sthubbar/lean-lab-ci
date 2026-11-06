import LeanLab.AlmostPrimeSums.Abel243
import LeanLab.AlmostPrimeSums.Kernel243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
The lower counterpart of the prime Abel calculation identifies the full
moving coefficient limit in BJS p. 54 equation 173.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Lower243

open Finset Real Filter Topology MeasureTheory
open LeanLab.ChenExplicit.D1552
open LeanLab.AlmostPrimeSums.Prime243 LeanLab.AlmostPrimeSums.Abel243
open LeanLab.AlmostPrimeSums.Decomp1527c

/-- Complementing an increasing nonnegative weight gives a lower prime Abel
estimate from the proved upper comparison and reciprocal prime error.
Derived symmetric estimate for BJS p. 54 equation 173. -/
theorem prime_abel_monotone_lower (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b)) (hfa : 0 ≤ f a) (hfb : 0 ≤ f b)
    (hf' : ∀ t ∈ Set.Icc a b, 0 ≤ f' t)
    (hfi : IntervalIntegrable (fun t => f t / (t * log t)) volume a b) :
    (∫ t in a..b, f t / (t * log t)) - 12 / log a * f b ≤
      ∑ p ∈ primesIco a b, f p / p := by
  let E := 6 / log a
  have hE : 0 ≤ E := by dsimp [E]; exact div_nonneg (by norm_num) (log_pos (by linarith)).le
  have hIa := Port1527c.Mertens.intervalIntegrable_one_div_mul_log ha
  have hIb := Port1527c.Mertens.intervalIntegrable_one_div_mul_log (ha.trans hab)
  have hOne := hIa.symm.trans hIb
  have hOneVal : (∫ t in a..b, 1 / (t * log t)) = log (log b) - log (log a) := by
    rw [← intervalIntegral.integral_interval_sub_left hIb hIa,
      Port1527c.Mertens.integral_one_div_mul_log (ha.trans hab),
      Port1527c.Mertens.integral_one_div_mul_log ha]
    ring
  have hg : ∀ t ∈ Set.Icc a b, HasDerivAt (fun u => f b - f u) (-f' t) t := by
    intro t ht
    simpa using (hf t ht).const_sub (f b)
  have hs := prime_abel_antitone_bound a b ha hab (primesIco a b)
    (by intro p hp; exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2,
      Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)⟩)
    (fun t => f b - f t) (fun t => -f' t) hg hfc.neg (by simp)
    (by intro t ht; exact neg_nonpos.mpr (hf' t ht))
  have hsum : (∑ p ∈ primesIco a b, (f b - f p) / p) =
      f b * (∑ p ∈ primesIco a b, (1 : ℝ) / p) - ∑ p ∈ primesIco a b, f p / p := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  have hInt : (∫ t in a..b, (f b - f t) / (t * log t)) =
      f b * (log (log b) - log (log a)) - ∫ t in a..b, f t / (t * log t) := by
    rw [show (fun t => (f b - f t) / (t * log t)) =
      (fun t => f b * (1 / (t * log t)) - f t / (t * log t)) by funext t; ring,
      intervalIntegral.integral_sub (hOne.const_mul (f b)) hfi,
      intervalIntegral.integral_const_mul, hOneVal]
  rw [hsum, hInt] at hs
  have hrecip := (abs_le.mp (prime_interval_error a b ha hab)).1
  have hlow : log (log b) - log (log a) - E ≤ ∑ p ∈ primesIco a b, (1 : ℝ) / p := by
    dsimp [E]
    linarith
  have hm := mul_le_mul_of_nonneg_left hlow hfb
  have hnonneg := mul_nonneg hE hfa
  have heq : 12 / log a * f b = 2 * E * f b := by dsimp [E]; ring
  rw [heq]
  change _ ≤ _ at hs
  change _ ≤ _ at hm
  dsimp [E] at hnonneg ⊢
  nlinarith only [hs, hm, hnonneg]

/-- The increasing logarithmic prime kernel has a lower estimate with a
fully proved Mertens error. Derived lower counterpart of BJS p. 54 equation 173. -/
theorem logarithmic_kernel_lower (a b L : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hL : log b < L) :
    ((log (log b) - log (L - log b)) - (log (log a) - log (L - log a))) / L -
      12 / (log a * (L - log b)) ≤
      ∑ p ∈ primesIco a b, 1 / ((p : ℝ) * (L - log p)) := by
  let f : ℝ → ℝ := fun t => 1 / (L - log t)
  let f' : ℝ → ℝ := fun t => t⁻¹ / (L - log t) ^ 2
  have htdata : ∀ t ∈ Set.Icc a b, 0 < t ∧ 0 < log t ∧ 0 < L - log t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hlog := log_le_log (by linarith : 0 < t) ht.2
    exact ⟨by linarith, log_pos ht1, by linarith⟩
  have hL0 : 0 < L := (htdata b ⟨hab, le_rfl⟩).2.1.trans hL
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t := by
    intro t ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have hh := ((hasDerivAt_const t L).sub (hasDerivAt_log ht0.ne')).inv hden0.ne'
    convert hh using 1
    · funext u; simp [f, one_div]
    · dsimp [f']; ring
  have hfc : ContinuousOn f' (Set.Icc a b) := by
    intro t ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have htne := ht0.ne'
    have hdenne := hden0.ne'
    have hden2 : (L - log t) ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
    have hh : ContinuousAt f' t := by dsimp [f']; fun_prop (disch := assumption)
    exact hh.continuousWithinAt
  have hcont : ContinuousOn (fun t => f t / (t * log t)) (Set.Icc a b) := by
    intro t ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have htne := ht0.ne'
    have hlogne := hlog0.ne'
    have hdenne := hden0.ne'
    have hproduct : t * log t ≠ 0 := mul_ne_zero htne hlogne
    have hh : ContinuousAt (fun t => f t / (t * log t)) t := by dsimp [f]; fun_prop (disch := assumption)
    exact hh.continuousWithinAt
  have hs := prime_abel_monotone_lower a b ha hab f f' hf hfc
    (by dsimp [f]; exact one_div_nonneg.mpr (htdata a ⟨le_rfl, hab⟩).2.2.le)
    (by dsimp [f]; exact one_div_nonneg.mpr (htdata b ⟨hab, le_rfl⟩).2.2.le)
    (by intro t ht; have ht0 := (htdata t ht).1; dsimp [f']; positivity)
    (hcont.intervalIntegrable_of_Icc hab)
  have hF : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => (log (log t) - log (L - log t)) / L) (f t / (t * log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have hh := (((hasDerivAt_log ht0.ne').log hlog0.ne').sub
      (((hasDerivAt_const t L).sub (hasDerivAt_log ht0.ne')).log hden0.ne')).div_const L
    convert hh using 1
    dsimp [f]
    field_simp [ht0.ne', hlog0.ne', hden0.ne', hL0.ne']
    <;> ring
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable_of_Icc hab)
  rw [hI] at hs
  convert hs using 1
  · dsimp [f]
    field_simp [hL0.ne', (htdata a ⟨le_rfl, hab⟩).2.1.ne', (htdata b ⟨hab, le_rfl⟩).2.2.ne']
    <;> ring
  · apply sum_congr rfl
    intro p hp
    dsimp [f]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]

/-- The moving sieve coefficient bounds the lower prime kernel.
Derived finite lower counterpart of BJS p. 54 equation 173. -/
theorem primeCoefficient_lower (N : ℕ) (B : ℝ) (hN : 2 ≤ N)
    (hz : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (hhalf : log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B) ≤
      4 * log ((N : ℝ) ^ ((1 : ℝ) / 8)))
    (hupper : log ((N : ℝ) ^ ((1 : ℝ) / 3)) <
      log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B)) :
    (let z := (N : ℝ) ^ ((1 : ℝ) / 8)
     let y := (N : ℝ) ^ ((1 : ℝ) / 3)
     let L := log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B)
     2 * exp eulerMascheroniConstant * log z *
       (((log (log y) - log (L - log y)) - (log (log z) - log (L - log z))) / L -
         12 / (log z * (L - log y)))) ≤ LeanLab.AlmostPrimeSums.Decomp243b.primeCoefficient N B := by
  let z := (N : ℝ) ^ ((1 : ℝ) / 8)
  let y := (N : ℝ) ^ ((1 : ℝ) / 3)
  let D := LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B
  let L := log D
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hD : 0 < D := by dsimp [D, LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel]; positivity
  have hzy : z ≤ y := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlogz : 0 < log z := log_pos (by change 2 ≤ z at hz; linarith)
  have hset : LeanLab.AlmostPrimeSums.Decomp243b.middlePrimes N = primesIco z y := rfl
  have hfac : 0 ≤ 2 * exp eulerMascheroniConstant * log z := by positivity
  have hpoint : ∀ q ∈ primesIco z y,
      (2 * exp eulerMascheroniConstant * log z) * (1 / ((q : ℝ) * (L - log q))) ≤
        LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (log (D / q) / log z) / ((q : ℝ) - 1) := by
    intro q hq
    obtain ⟨hqmem, hqprime, hzq⟩ := mem_filter.mp hq
    have hqy : (q : ℝ) < y := Nat.lt_ceil.mp (mem_range.mp hqmem)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hq1 : 0 < (q : ℝ) - 1 := by change 2 ≤ z at hz; linarith
    have hloglow : log z ≤ log (q : ℝ) := log_le_log hz0 hzq
    have hloghigh : log (q : ℝ) ≤ log y := log_le_log hq0 hqy.le
    have hden : 0 < L - log q := by dsimp [L, D]; linarith
    have hs3 : log (D / q) / log z ≤ 3 := by
      rw [log_div hD.ne' hq0.ne', div_le_iff₀ hlogz]
      change log D ≤ 4 * log z at hhalf
      linarith
    have hratio : 1 ≤ (q : ℝ) / (q - 1) := (le_div_iff₀ hq1).mpr (by linarith)
    have heq : LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (log (D / q) / log z) / ((q : ℝ) - 1) =
        (2 * exp eulerMascheroniConstant * log z) * ((q : ℝ) / (q - 1)) *
          (1 / ((q : ℝ) * (L - log q))) := by
      rw [LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve, ite_eq_left hs3, log_div hD.ne' hq0.ne']
      dsimp [L]
      field_simp [hlogz.ne', hq0.ne', hq1.ne', hden.ne']
    rw [heq]
    calc
      _ = (2 * exp eulerMascheroniConstant * log z) * 1 *
          (1 / ((q : ℝ) * (L - log q))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hfac) (by positivity)
  have hsum := sum_le_sum hpoint
  rw [← mul_sum] at hsum
  have hkernel := logarithmic_kernel_lower z y L hz hzy hupper
  have hbound := (mul_le_mul_of_nonneg_left hkernel hfac).trans hsum
  simpa only [LeanLab.AlmostPrimeSums.Decomp243b.primeCoefficient, hset, z, y, D, L] using hbound

noncomputable section
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243b
open LeanLab.AlmostPrimeSums.Kernel243

/-- The normalized lower logarithmic kernel with its coarse Mertens error.
Derived lower envelope for the limit in BJS p. 54 equation 173. -/
def kernelLower (N : ℕ) (B : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant *
    ((log (8 / 3 : ℝ) + log ((levelRatio N B - 1 / 8) / (levelRatio N B - 1 / 3))) /
      (8 * levelRatio N B) - 12 / ((levelRatio N B - 1 / 3) * log N))

/-- The lower kernel has the same limiting coefficient as the upper envelope.
Derived lower limit evaluation for BJS p. 54 equation 173. -/
theorem kernelLower_limit (B : ℝ) :
    Tendsto (fun N : ℕ => kernelLower N B) atTop
      (𝓝 (exp eulerMascheroniConstant * log 6 / 2)) := by
  have hk := levelRatio_limit B
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hq := ((hk.sub_const (1 / 8)).div (hk.sub_const (1 / 3)) (by norm_num)).log (by norm_num)
  have hmain := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => log (8 / 3 : ℝ))
    atTop (𝓝 (log (8 / 3 : ℝ)))).add hq).div (hk.const_mul 8) (by norm_num)
  have hden := (hk.sub_const (1 / 3)).pos_mul_atTop (by norm_num) hlog
  have herr := hden.const_div_atTop (12 : ℝ)
  have h := (hmain.sub herr).const_mul (2 * exp eulerMascheroniConstant)
  have hlogs : log (8 / 3 : ℝ) + log (9 / 4 : ℝ) = log 6 := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num only at h
  rw [hlogs] at h
  convert h using 1 <;> try funext N
  all_goals try dsimp [kernelLower]
  all_goals ring

/-- The moving coefficient is eventually above its explicit lower envelope.
Derived lower application of BJS p. 54 equation 173. -/
theorem primeCoefficient_ge_envelope (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, kernelLower N B ≤ primeCoefficient N B := by
  have hk := (levelRatio_limit B).eventually (lt_mem_nhds (by norm_num : (1 / 3 : ℝ) < 1 / 2))
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually_ge_atTop 1,
    hz.eventually_ge_atTop 2, hk] with N hN hlog1 hz2 hkN
  let k := levelRatio N B
  let l := log (N : ℝ)
  let z := (N : ℝ) ^ ((1 : ℝ) / 8)
  let y := (N : ℝ) ^ ((1 : ℝ) / 3)
  let L := log (sieveLevel N B)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < l := by dsimp [l]; linarith
  have hD : 0 < sieveLevel N B := by dsimp [sieveLevel]; positivity
  have hzlog : log z = l / 8 := by dsimp [z, l]; rw [log_rpow hNp]; ring
  have hylog : log y = l / 3 := by dsimp [y, l]; rw [log_rpow hNp]; ring
  have hL : L = k * l := by dsimp [L, k, l, levelRatio]; field_simp [hl.ne']
  have hk3 : 0 < k - 1 / 3 := by dsimp [k]; linarith
  have hk8 : 0 < k - 1 / 8 := by linarith
  have hk0 : 0 < k := by linarith
  have hhalf : L ≤ 4 * log z := by
    dsimp [L, sieveLevel]
    rw [log_div (sqrt_pos_of_pos hNp).ne' (rpow_pos_of_pos hl B).ne',
      log_sqrt hNp.le, log_rpow hl, hzlog]
    have hh : 0 ≤ B * log l := mul_nonneg hB.le (log_nonneg hlog1)
    change log (N : ℝ) / 2 - B * log (log N) ≤ 4 * (l / 8)
    dsimp [l] at *
    linarith
  have hupper : log y < L := by rw [hylog, hL]; nlinarith
  have hbound := primeCoefficient_lower N B hN hz2 hhalf hupper
  have heq : 2 * exp eulerMascheroniConstant * log z *
      (((log (log y) - log (L - log y)) -
        (log (log z) - log (L - log z))) / L - 12 / (log z * (L - log y))) = kernelLower N B := by
    rw [hzlog, hylog, hL,
      show k * l - l / 3 = (k - 1 / 3) * l by ring,
      show k * l - l / 8 = (k - 1 / 8) * l by ring,
      log_div hl.ne' (by norm_num), log_div hl.ne' (by norm_num),
      log_mul hk3.ne' hl.ne', log_mul hk8.ne' hl.ne']
    dsimp [kernelLower]
    change _ = 2 * exp eulerMascheroniConstant *
      ((log (8 / 3 : ℝ) + log ((k - 1 / 8) / (k - 1 / 3))) / (8 * k) - 12 / ((k - 1 / 3) * l))
    rw [log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num), log_div hk8.ne' hk3.ne']
    field_simp [hl.ne', hk0.ne', hk3.ne']
    <;> ring
  rw [← heq]
  exact hbound

/-- The exact moving prime coefficient limit is now supplied from both Abel
bounds. BJS p. 54 equation 173 with the logarithmic level loss tending to zero. -/
theorem primeCoefficient_limit (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N : ℕ => primeCoefficient N B) atTop
      (𝓝 (exp eulerMascheroniConstant * log 6 / 2)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (kernelLower_limit B) (kernelEnvelope_limit B)
    (primeCoefficient_ge_envelope B hB) (primeCoefficient_le_envelope B hB)

end

end LeanLab.AlmostPrimeSums.Lower243
