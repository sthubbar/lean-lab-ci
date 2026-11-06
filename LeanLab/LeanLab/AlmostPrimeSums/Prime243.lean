import LeanLab.AlmostPrimeSums.Base243
import LeanLab.ChenExplicit.Decomp1552a

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Strict prime interval endpoints and the unconditional qualitative Abel input
needed by BJS p. 54 equation 173. The error is weaker than the explicit
Dusart error used by Yamada. It tends to zero and assumes no cited prime bound.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Prime243

open Finset Real Filter Topology
open LeanLab.ChenExplicit.D1552

/-- Exchanging the two endpoint conventions for reciprocal prime sums costs
at most two divided by the lower endpoint. Derived cutoff bookkeeping for
BJS p. 54 equation 173 and its use of the Mertens estimate. -/
theorem prime_endpoint_error (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    |(∑ p ∈ primesIco a b, (1 : ℝ) / p) -
      ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p| ≤ 2 / a := by
  classical
  let S := primesIco a b
  let T := (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime
  have hb : 0 < b := ha.trans_le hab
  have hS (p : ℕ) : p ∈ S ↔ p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b := by
    simp only [S, primesIco, mem_filter, mem_range, Nat.lt_ceil]
    tauto
  have hT (p : ℕ) : p ∈ T ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    simp only [T, mem_filter, mem_Ioc, Nat.floor_lt ha.le, Nat.le_floor_iff hb.le]
    tauto
  have hleft : ∀ p ∈ S \ T, (p : ℝ) = a := by
    intro p hp
    obtain ⟨hpS, hpT⟩ := mem_sdiff.mp hp
    obtain ⟨hpr, hpa, hpb⟩ := (hS p).mp hpS
    have hn : ¬ a < (p : ℝ) := by
      intro h
      exact hpT ((hT p).mpr ⟨hpr, h, hpb.le⟩)
    linarith
  have hright : ∀ p ∈ T \ S, (p : ℝ) = b := by
    intro p hp
    obtain ⟨hpT, hpS⟩ := mem_sdiff.mp hp
    obtain ⟨hpr, hpa, hpb⟩ := (hT p).mp hpT
    have hn : ¬ (p : ℝ) < b := by
      intro h
      exact hpS ((hS p).mpr ⟨hpr, hpa.le, h⟩)
    linarith
  have hcardL : #(S \ T) ≤ 1 := card_le_one.mpr (by
    intro p hp q hq
    exact_mod_cast (hleft p hp).trans (hleft q hq).symm)
  have hcardR : #(T \ S) ≤ 1 := card_le_one.mpr (by
    intro p hp q hq
    exact_mod_cast (hright p hp).trans (hright q hq).symm)
  have hsmall (E : Finset ℕ) (hcard : #E ≤ 1) (hmin : ∀ p ∈ E, a ≤ (p : ℝ)) :
      (∑ p ∈ E, (1 : ℝ) / p) ≤ 1 / a := by
    calc
      _ ≤ ∑ _p ∈ E, (1 : ℝ) / a := sum_le_sum (fun p hp =>
        one_div_le_one_div_of_le ha (hmin p hp))
      _ = (#E : ℝ) * (1 / a) := by simp
      _ ≤ 1 * (1 / a) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := one_mul _
  have hL := hsmall (S \ T) hcardL (fun p hp => by rw [hleft p hp])
  have hR := hsmall (T \ S) hcardR (fun p hp => by rw [hright p hp]; exact hab)
  have heq : (∑ p ∈ S, (1 : ℝ) / p) - ∑ p ∈ T, (1 : ℝ) / p =
      (∑ p ∈ S \ T, (1 : ℝ) / p) - ∑ p ∈ T \ S, (1 : ℝ) / p :=
    sum_sdiff_sub_sum_sdiff.symm
  change |(∑ p ∈ S, (1 : ℝ) / p) - ∑ p ∈ T, (1 : ℝ) / p| ≤ _
  rw [heq]
  have hnL : 0 ≤ ∑ p ∈ S \ T, (1 : ℝ) / p := sum_nonneg (fun _ _ => by positivity)
  have hnR : 0 ≤ ∑ p ∈ T \ S, (1 : ℝ) / p := sum_nonneg (fun _ _ => by positivity)
  rw [show (2 : ℝ) / a = 2 * (1 / a) by ring, abs_le]
  constructor <;> linarith

/-- A fully proved reciprocal prime interval estimate for strict upper endpoints.
Derived weaker error for the Mertens input in BJS p. 54 equation 173. -/
theorem prime_interval_error (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    |(∑ p ∈ primesIco a b, (1 : ℝ) / p) - (log (log b) - log (log a))| ≤ 6 / log a := by
  have ha0 : 0 < a := by linarith
  have hla : 0 < log a := log_pos (by linarith)
  have hM := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block ha hab
  have hE := prime_endpoint_error a b ha0 hab
  have htotal : |(∑ p ∈ primesIco a b, (1 : ℝ) / p) - (log (log b) - log (log a))| ≤
      2 / a + 4 / log a := by
    calc
      _ ≤ |(∑ p ∈ primesIco a b, (1 : ℝ) / p) -
          ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p| +
        |(∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
          (log (log b) - log (log a))| := by
        convert abs_add_le
          ((∑ p ∈ primesIco a b, (1 : ℝ) / p) -
            ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p)
          ((∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
            (log (log b) - log (log a))) using 1 <;> ring
      _ ≤ _ := add_le_add hE hM
  have hinv : 1 / a ≤ 1 / log a := one_div_le_one_div_of_le hla
    (by have := log_le_sub_one_of_pos ha0; linarith)
  simp only [div_eq_mul_inv, one_mul] at htotal hinv ⊢
  linarith only [htotal, hinv]

/-- A uniform qualitative Abel input on every sufficiently far out interval.
The interval may have any length. Derived from the Mertens input used at
BJS p. 54 equation 173. -/
theorem prime_interval_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ a b : ℝ, A ≤ a → a ≤ b →
      |(∑ p ∈ primesIco a b, (1 : ℝ) / p) - (log (log b) - log (log a))| < ε := by
  have hlim : Tendsto (fun a : ℝ => 6 / log a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max A 2, le_max_right _ _, fun a b ha hab => ?_⟩
  exact (prime_interval_error a b ((le_max_right _ _).trans ha) hab).trans_lt
    (hA a ((le_max_left _ _).trans ha))

/-- The increasing smooth prime Abel comparison with a proved Mertens error.
This supplies a weaker unconditional version of the interval hypothesis used
for BJS p. 54 equation 173. -/
theorem prime_abel_monotone_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b))
    (hfa : 0 ≤ f a) (hf' : ∀ t ∈ Set.Icc a b, 0 ≤ f' t) :
    ∑ p ∈ s, f p / p ≤ (∫ t in a..b, f t / (t * log t)) + 6 / log a * f b := by
  apply prime_abel_monotone a b (6 / log a) (by linarith) hab s hs f f' hf hfc hfa hf'
  intro x y hax hxy _hyb
  have hx2 : 2 ≤ x := ha.trans hax
  have h := (le_abs_self _).trans (prime_interval_error x y hx2 hxy)
  have hlog : 0 < log a := log_pos (by linarith)
  have hle : 6 / log x ≤ 6 / log a := by
    apply div_le_div_of_nonneg_left (by norm_num) hlog
    exact log_le_log (by linarith) hax
  linarith

/-- Explicit increasing logarithmic kernel bound with a proved reciprocal
prime error. This is the prime Abel calculation in BJS p. 54 equation 173,
for a general level logarithm L above log of the upper endpoint. -/
theorem logarithmic_kernel_bound (a b L : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hL : log b < L) :
    (∑ p ∈ primesIco a b, 1 / ((p : ℝ) * (L - log p))) ≤
      ((log (log b) - log (L - log b)) -
        (log (log a) - log (L - log a))) / L + 6 / (log a * (L - log b)) := by
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
  have hsum := prime_abel_monotone_bound a b ha hab (primesIco a b)
    (by
      intro p hp
      exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2,
        Nat.lt_ceil.mp (mem_range.mp (mem_filter.mp hp).1)⟩)
    f f' hf hfc
    (by dsimp [f]; exact one_div_nonneg.mpr (htdata a ⟨le_rfl, hab⟩).2.2.le)
    (by intro t ht; have ht0 := (htdata t ht).1; dsimp [f']; positivity)
  have hcont : ContinuousOn (fun t => f t / (t * log t)) (Set.Icc a b) := by
    intro t ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have htne := ht0.ne'
    have hlogne := hlog0.ne'
    have hdenne := hden0.ne'
    have hproduct : t * log t ≠ 0 := mul_ne_zero htne hlogne
    have hh : ContinuousAt (fun t => f t / (t * log t)) t := by
      dsimp [f]
      fun_prop (disch := assumption)
    exact hh.continuousWithinAt
  have hF : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => (log (log t) - log (L - log t)) / L)
        (f t / (t * log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlog0, hden0⟩ := htdata t ht
    have hh := (((hasDerivAt_log ht0.ne').log hlog0.ne').sub
      (((hasDerivAt_const t L).sub (hasDerivAt_log ht0.ne')).log hden0.ne')).div_const L
    convert hh using 1
    dsimp [f]
    field_simp [ht0.ne', hlog0.ne', hden0.ne', hL0.ne']
    <;> ring
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hcont.intervalIntegrable_of_Icc hab)
  rw [hI] at hsum
  convert hsum using 1
  · apply sum_congr rfl
    intro p hp
    dsimp [f]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  · dsimp [f]
    field_simp [hL0.ne', (htdata a ⟨le_rfl, hab⟩).2.1.ne',
      (htdata b ⟨hab, le_rfl⟩).2.2.ne']
    <;> ring

/-- Finite upper bound for the moving prime coefficient by its explicit
logarithmic integral and a proved vanishing error. BJS p. 54 equation 173.
The assumptions put every sieve parameter in the closed form range of F. -/
theorem primeCoefficient_bound (N : ℕ) (B : ℝ) (hN : 2 ≤ N)
    (hz : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (hhalf : log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B) ≤
      4 * log ((N : ℝ) ^ ((1 : ℝ) / 8)))
    (hupper : log ((N : ℝ) ^ ((1 : ℝ) / 3)) <
      log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B)) :
    LeanLab.AlmostPrimeSums.Decomp243b.primeCoefficient N B ≤
      let z := (N : ℝ) ^ ((1 : ℝ) / 8)
      let y := (N : ℝ) ^ ((1 : ℝ) / 3)
      let L := log (LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B)
      2 * exp eulerMascheroniConstant * log z * (z / (z - 1)) *
        (((log (log y) - log (L - log y)) -
          (log (log z) - log (L - log z))) / L + 6 / (log z * (L - log y))) := by
  let z := (N : ℝ) ^ ((1 : ℝ) / 8)
  let y := (N : ℝ) ^ ((1 : ℝ) / 3)
  let D := LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel N B
  let L := log D
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hD : 0 < D := by
    dsimp [D, LeanLab.AlmostPrimeSums.Decomp243a.sieveLevel]
    positivity
  have hzy : z ≤ y := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hz1 : 0 < z - 1 := by change 2 ≤ z at hz; linarith
  have hlogz : 0 < log z := log_pos (by change 2 ≤ z at hz; linarith)
  have hset : LeanLab.AlmostPrimeSums.Decomp243b.middlePrimes N = primesIco z y := rfl
  have hfac : 0 ≤ 2 * exp eulerMascheroniConstant * log z * (z / (z - 1)) := by positivity
  have hpoint : ∀ q ∈ primesIco z y,
      LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (log (D / q) / log z) / ((q : ℝ) - 1) ≤
        (2 * exp eulerMascheroniConstant * log z * (z / (z - 1))) *
          (1 / ((q : ℝ) * (L - log q))) := by
    intro q hq
    obtain ⟨hqmem, hqprime, hzq⟩ := mem_filter.mp hq
    have hqy : (q : ℝ) < y := Nat.lt_ceil.mp (mem_range.mp hqmem)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
    have hq1 : 0 < (q : ℝ) - 1 := by linarith
    have hloglow : log z ≤ log (q : ℝ) := log_le_log hz0 hzq
    have hloghigh : log (q : ℝ) ≤ log y := log_le_log hq0 hqy.le
    have hden : 0 < L - log q := by dsimp [L, D]; linarith
    have hs3 : log (D / q) / log z ≤ 3 := by
      rw [log_div hD.ne' hq0.ne', div_le_iff₀ hlogz]
      change log D ≤ 4 * log z at hhalf
      linarith
    have hratio : (q : ℝ) / (q - 1) ≤ z / (z - 1) := by
      rw [div_le_div_iff₀ hq1 hz1]
      nlinarith
    have heq : LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve (log (D / q) / log z) /
        ((q : ℝ) - 1) =
        (2 * exp eulerMascheroniConstant * log z) * ((q : ℝ) / (q - 1)) *
          (1 / ((q : ℝ) * (L - log q))) := by
      rw [LeanLab.AlmostPrimeSums.Decomp1527a.Fsieve, ite_eq_left hs3,
        log_div hD.ne' hq0.ne']
      dsimp [L]
      field_simp [hlogz.ne', hq0.ne', hq1.ne', hden.ne']
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (by positivity)) (by positivity)
  have hsum := sum_le_sum hpoint
  rw [← mul_sum] at hsum
  have hkernel := logarithmic_kernel_bound z y L hz hzy hupper
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left hkernel hfac)
  simpa only [LeanLab.AlmostPrimeSums.Decomp243b.primeCoefficient, hset,
    z, y, D, L] using hbound

end LeanLab.AlmostPrimeSums.Prime243
