/-
P0072 A. Togashi and S. Uchiyama 1964, J. Fac. Sci. Hokkaido Univ. Ser. I 18, pp. 60 to 68.
Lab copy papers/P0072.pdf and papers/P0072.txt. Unit U-1544, run 20261026T0808Z-17522, type
DECOMPOSE, track T1, file c of three.

This file c proves the summed upper sieve input of Section 3, pp. 64 to 65.
The three leaves open at the start of CODEX task213 now have proofs. The final P0072
statement remains CONDITIONAL ON Lemma 4, `LowerSieveInput`, alone. Older declaration
doc comments retain their original decomposition dependency lists.

Steps: for q ∈ Qset N put t_q = log N/log q ∈ [3, 6), a = 3(1 - 2ε - 1/t_q) ∈ (1, 3] and
w = N^{a/6}, so the sieve level is w² = N^{1-2ε}/q. Then
S(q) ≤ 2φ(N)/(q W_q) + R_q, W_q ≥ (1 - δ)((2a - 1)² - 2a² log a)/36 · C_N log² N, and
2φ(N)/(q · ((2a - 1)² - 2a² log a)/36 · C_N log² N) = A_N C_ε(t_q) φ(N)/(q log² N), p. 65.
Summing, Σ_q C_ε(t_q)/q ≤ I(ε) + o(1), "just as in [6, §5]", p. 65, and the remainders are
o(φ(N)/log² N) because B_N = 2^{ν(N)} = N^{o(1)}.

Original leaves, all now supplied with proofs: `prime_sum_integral`, `two_pow_omega_le`, `Q_large`, `logpow_le_rpow`.
Assemblies, no sorry of their own: `remainder_small`, `Wq_relative`, `Sq_le_main`,
`upperSieveInput_of_leaves`, `togashiUchiyama_of_lemma4`.

Original decomposition by Claude, 2026-10-26. Proofs and extensions by CODEX task213,
2026-11-01. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.AlmostPrimeSums.Decomp1544b

open Finset Real Filter Topology
open scoped ArithmeticFunction.omega

noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp1544c
open LeanLab.AlmostPrimeSums.TogashiUchiyamaSection5 LeanLab.AlmostPrimeSums.Decomp1544a
open LeanLab.AlmostPrimeSums.Decomp1544b LeanLab.AlmostPrimeSums.TogashiUchiyamaScale
open LeanLab.AlmostPrimeSums.TogashiUchiyamaConvex

/-- Derived local logarithm bound for the odd prime product on p. 61. -/
lemma log_odd_factor_lower {p : ℝ} (hp : 3 ≤ p) :
    -(10 / p) ≤ log ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hm0 : 0 < p - 2 := by linarith
  have h := one_sub_inv_le_log_of_pos (div_pos hm0 hp0)
  have he : 1 - ((p - 2) / p)⁻¹ = -(2 / (p - 2)) := by
    field_simp [hp0.ne', hm0.ne'] <;> ring
  rw [he] at h
  have hle : 2 / (p - 2) ≤ 10 / p := by
    rw [div_le_div_iff₀ hm0 hp0]
    linarith
  linarith

/-- Derived weak product bound for p. 61. The proved reciprocal prime factor estimate
suffices for the relative error on p. 64 without an exact Mertens constant. -/
lemma log_Q_lower {N : ℕ} (hN : 2 ≤ N) :
    -(10 * (3 ^ 40 : ℝ) + 22) - (1 / 4 : ℝ) * log (log N) ≤ log (Q N) := by
  have hlocal : ∀ p ∈ N.primeFactors.filter (2 < ·),
      -(10 / (p : ℝ)) ≤ log (((p : ℝ) - 2) / p) := by
    intro p hp
    apply log_odd_factor_lower
    exact_mod_cast (show 3 ≤ p from (mem_filter.mp hp).2)
  have hprod : log (Q N) =
      ∑ p ∈ N.primeFactors.filter (2 < ·), log (((p : ℝ) - 2) / p) := by
    unfold Q
    apply log_prod
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact (div_pos (by linarith) (by linarith)).ne'
  rw [hprod]
  have hs := sum_le_sum hlocal
  rw [sum_neg_distrib] at hs
  have hsub : ∑ p ∈ N.primeFactors.filter (2 < ·), 10 / (p : ℝ) ≤
      ∑ p ∈ N.primeFactors, 10 / (p : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro p _ _
    positivity
  have hb := prime_recip_sum_bound N hN
  linarith

/-- Derived change of variables for the prime window on pp. 63 to 65. -/
lemma prime_log_window {N q : ℕ} (hN : 2 ≤ N) (hq : q.Prime) :
    (N < q ^ 6 ∧ q ^ 3 ≤ N) ↔ 3 ≤ log N / log q ∧ log N / log q < 6 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hq.one_lt)
  have hp6 : log ((q ^ 6 : ℕ) : ℝ) = 6 * log q := by simp [log_pow]
  have hp3 : log ((q ^ 3 : ℕ) : ℝ) = 3 * log q := by simp [log_pow]
  rw [le_div_iff₀ hlq, div_lt_iff₀ hlq]
  constructor
  · rintro ⟨h6, h3⟩
    have h6R : (N : ℝ) < (q ^ 6 : ℕ) := by exact_mod_cast h6
    have h3R : ((q ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast h3
    have h6' := log_lt_log hNR h6R
    have h3' := log_le_log (by exact_mod_cast pow_pos hq.pos 3) h3R
    rw [hp6] at h6'
    rw [hp3] at h3'
    exact ⟨h3', by linarith⟩
  · rintro ⟨h3, h6⟩
    have h6R : (N : ℝ) < (q ^ 6 : ℕ) := by
      apply (log_lt_log_iff hNR (by exact_mod_cast pow_pos hq.pos 6)).mp
      rw [hp6]
      linarith
    have h3R : ((q ^ 3 : ℕ) : ℝ) ≤ N := by
      apply (log_le_log_iff (by exact_mod_cast pow_pos hq.pos 3) hNR).mp
      rw [hp3]
      exact h3
    exact ⟨by exact_mod_cast h6R, by exact_mod_cast h3R⟩

/-- Derived exact cutoff identity for each short prime block on p. 65. -/
lemma prime_block_eq {N : ℕ} (hN : 2 ≤ N) {a b : ℝ}
    (ha : 3 ≤ a) (hab : a < b) (hb : b ≤ 6) :
    ((range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N)).filter
      (fun q : ℕ => a ≤ log N / log q ∧ log N / log q < b) =
    (Ioc ⌊exp (log N / b)⌋₊ ⌊exp (log N / a)⌋₊).filter Nat.Prime := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  ext q
  simp only [mem_filter, mem_range, mem_Ioc]
  by_cases hqp : q.Prime
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hqp.one_lt)
    have hcut : (⌊exp (log N / b)⌋₊ < q ∧ q ≤ ⌊exp (log N / a)⌋₊) ↔
        a ≤ log N / log q ∧ log N / log q < b := by
      rw [Nat.floor_lt (exp_pos _).le, Nat.le_floor_iff (exp_pos _).le,
        ← lt_log_iff_exp_lt hq0, ← log_le_iff_le_exp hq0,
        div_lt_iff₀ hb0, le_div_iff₀ ha0,
        le_div_iff₀ hlq, div_lt_iff₀ hlq]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith
    have hwindow := prime_log_window hN hqp
    constructor
    · rintro ⟨⟨_, _, _⟩, ht⟩
      exact ⟨hcut.mpr ht, hqp⟩
    · rintro ⟨hcut', _⟩
      have ht := hcut.mp hcut'
      have hwin := hwindow.mpr ⟨ha.trans ht.1, ht.2.trans_le hb⟩
      have hqN : q ≤ N := by
        have : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
        exact this.trans hwin.2
      exact ⟨⟨by omega, hqp, hwin⟩, ht⟩
  · simp [hqp]

/-- Derived Mertens limit on each fixed short block in the p. 65 change of variables. -/
lemma prime_block_tendsto {a b : ℝ} (ha : 3 ≤ a) (hab : a < b) (hb : b ≤ 6) :
    Tendsto (fun N : ℕ => ∑ q ∈
      ((range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N)).filter
        (fun q : ℕ => a ≤ log N / log q ∧ log N / log q < b), (1 : ℝ) / q)
      atTop (𝓝 (log (b / a))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun N : ℕ => 4 * b / log (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop (b * log 2),
    herr.eventually (gt_mem_nhds hε)] with N hN hL hsmall
  have hL0 : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hy : (2 : ℝ) ≤ exp (log N / b) := by
    rw [← log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2), le_div_iff₀ hb0]
    nlinarith
  have hyx : exp (log N / b) ≤ exp (log N / a) := by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_left hL0.le ha0 hab.le
  have hm := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy hyx
  simp only [log_exp] at hm
  have hmain : log (log N / a) - log (log N / b) = log (b / a) := by
    rw [log_div hL0.ne' ha0.ne', log_div hL0.ne' hb0.ne', log_div hb0.ne' ha0.ne']
    ring
  have he : 4 / (log (N : ℝ) / b) = 4 * b / log N := by field_simp
  rw [hmain, he] at hm
  rw [Real.dist_eq, prime_block_eq hN ha hab hb]
  exact hm.trans_lt hsmall

/-- Derived finite block partition for the prime sum on p. 65. -/
lemma sum_short_blocks (s : Finset ℕ) (t f : ℕ → ℝ) (a : ℕ → ℝ)
    (ha : Monotone a) (n : ℕ) :
    (∑ i ∈ range n, ∑ q ∈ s.filter (fun q => a i ≤ t q ∧ t q < a (i + 1)), f q) =
      ∑ q ∈ s.filter (fun q => a 0 ≤ t q ∧ t q < a n), f q := by
  induction n with
  | zero =>
    have he : s.filter (fun q => a 0 ≤ t q ∧ t q < a 0) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro q _ hq
      exact (not_lt_of_ge hq.1) hq.2
    simp [he]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp only [sum_filter]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro q _hq
    have h0 := ha (show 0 ≤ n from Nat.zero_le _)
    have h1 := ha (show n ≤ n + 1 from Nat.le_succ _)
    by_cases hA : a 0 ≤ t q <;> by_cases hB : t q < a n <;>
      by_cases hC : t q < a (n + 1) <;>
      by_cases hD : a n ≤ t q <;> simp_all <;> linarith

/-- Derived continuous test function argument for p. 65 from its short block limits. -/
theorem continuous_test_of_blocks
    (s : ℕ → Finset ℕ) (t w : ℕ → ℕ → ℝ)
    (hw : ∀ N q, q ∈ s N → 0 ≤ w N q)
    (ht : ∀ N q, q ∈ s N → 3 ≤ t N q ∧ t N q < 6)
    (hb : ∀ a b : ℝ, 3 ≤ a → a < b → b ≤ 6 →
      Tendsto (fun N => ∑ q ∈ (s N).filter (fun q => a ≤ t N q ∧ t N q < b), w N q)
        atTop (𝓝 (log (b / a))))
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 3 6)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∑ q ∈ s N, φ (t N q) * w N q ≤
      (∫ u in (3 : ℝ)..6, φ u / u) + η := by
  let ε := η / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / δ)
  have hn0 : 0 < n := by
    have : 0 < (n : ℝ) := lt_trans (by positivity : (0 : ℝ) < 3 / δ) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let a : ℕ → ℝ := fun i => 3 + 3 * i / n
  have ha : Monotone a := by
    intro i j hij
    dsimp [a]
    gcongr
  have ha0 : a 0 = 3 := by simp [a]
  have han : a n = 6 := by dsimp [a]; field_simp [hnR.ne'] <;> ring
  have hai : ∀ i, i ≤ n → a i ∈ Set.Icc (3 : ℝ) 6 := by
    intro i hi
    constructor
    · rw [← ha0]; exact ha (Nat.zero_le i)
    · rw [← han]; exact ha hi
  have hstep : ∀ i, a (i + 1) - a i = 3 / (n : ℝ) := by
    intro i
    dsimp [a]
    push_cast
    ring
  have has : ∀ i, a i < a (i + 1) := by
    intro i
    have hpos : 0 < 3 / (n : ℝ) := by positivity
    linarith [hstep i]
  have hosc : ∀ i < n, ∀ u ∈ Set.Icc (a i) (a (i + 1)),
      |φ (a i) - φ u| < ε := by
    intro i hi u hu
    have hi' := hai i (by omega)
    have hi1 := hai (i + 1) (by omega)
    have hu' : u ∈ Set.Icc (3 : ℝ) 6 := ⟨hi'.1.trans hu.1, hu.2.trans hi1.2⟩
    rw [← Real.dist_eq]
    apply hmod (a i) hi' u hu'
    rw [Real.dist_eq]
    have hmesh : a (i + 1) - a i < δ := by
      rw [hstep]
      have hh : 3 < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
      exact (div_lt_iff₀ hnR).mpr (by nlinarith)
    rw [abs_of_nonpos (by linarith [hu.1] : a i - u ≤ 0)]
    linarith [hu.2]
  let L : ℝ := ∑ i ∈ range n, (φ (a i) + ε) * log (a (i + 1) / a i)
  have hlim : Tendsto (fun N => ∑ i ∈ range n, (φ (a i) + ε) *
      ∑ q ∈ (s N).filter (fun q => a i ≤ t N q ∧ t N q < a (i + 1)), w N q)
      atTop (𝓝 L) := by
    apply tendsto_finsetSum
    intro i hi
    exact (hb (a i) (a (i + 1)) (hai i (by have := mem_range.mp hi; omega)).1
      (has i) (hai (i + 1) (by have := mem_range.mp hi; omega)).2).const_mul _
  have hint : IntervalIntegrable (fun u => φ u / u) MeasureTheory.volume 3 6 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hφ.div continuousOn_id (fun u hu => by linarith [hu.1])
  have hintcell : ∀ i < n, IntervalIntegrable (fun u => φ u / u) MeasureTheory.volume
      (a i) (a (i + 1)) := by
    intro i hi
    apply hint.mono_set
    rw [Set.uIcc_of_le (has i).le, Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 6)]
    exact Set.Icc_subset_Icc (hai i (by omega)).1 (hai (i + 1) (by omega)).2
  have hL : L ≤ (∫ u in (3 : ℝ)..6, φ u / u) + 2 * ε := by
    have hcell : ∀ i < n, (φ (a i) + ε) * log (a (i + 1) / a i) ≤
        (∫ u in a i..a (i + 1), φ u / u) + 2 * ε * log (a (i + 1) / a i) := by
      intro i hi
      have hi0 : 0 < a i := by have := (hai i (by omega)).1; linarith
      have hi10 : 0 < a (i + 1) := by linarith [has i]
      have hcont : ContinuousOn (fun u : ℝ => 1 / u) (Set.Icc (a i) (a (i + 1))) :=
        continuousOn_const.div continuousOn_id (fun u hu => by linarith [hu.1])
      have hmono := intervalIntegral.integral_mono_on (has i).le
        ((hcont.const_mul (φ (a i) + ε)).intervalIntegrable_of_Icc (has i).le)
        ((hintcell i hi).add ((hcont.const_mul (2 * ε)).intervalIntegrable_of_Icc (has i).le))
        (fun u hu => show (φ (a i) + ε) * (1 / u) ≤ φ u / u + 2 * ε * (1 / u) from by
          have hh := (abs_lt.mp (hosc i hi u hu)).2
          have hu0 : 0 < u := hi0.trans_le hu.1
          rw [show φ u / u = φ u * (1 / u) by ring]
          nlinarith [mul_nonneg (show 0 ≤ φ u + 2 * ε - (φ (a i) + ε) by linarith)
            (show 0 ≤ 1 / u by positivity)])
      simpa only [intervalIntegral.integral_add (hintcell i hi)
        ((hcont.const_mul (2 * ε)).intervalIntegrable_of_Icc (has i).le),
        intervalIntegral.integral_const_mul, integral_one_div_of_pos hi0 hi10] using hmono
    have hsum := sum_le_sum (fun i hi => hcell i (mem_range.mp hi))
    have htel := intervalIntegral.sum_integral_adjacent_intervals hintcell
    have hlogtel : ∑ i ∈ range n, log (a (i + 1) / a i) = log 2 := by
      have hh : ∀ i < n, IntervalIntegrable (fun u : ℝ => 1 / u)
          MeasureTheory.volume (a i) (a (i + 1)) := by
        intro i hi
        apply ContinuousOn.intervalIntegrable_of_Icc (has i).le
        exact continuousOn_const.div continuousOn_id (fun u hu => by
          have := (hai i (by omega)).1; linarith [hu.1])
      calc ∑ i ∈ range n, log (a (i + 1) / a i)
          = ∑ i ∈ range n, ∫ u in a i..a (i + 1), (1 : ℝ) / u := by
              apply sum_congr rfl
              intro i hi
              have hi' := mem_range.mp hi
              exact (integral_one_div_of_pos
                (by have := (hai i (by omega)).1; linarith)
                (by have := (hai (i + 1) (by omega)).1; linarith)).symm
        _ = ∫ u in (3 : ℝ)..6, 1 / u := by
              rw [intervalIntegral.sum_integral_adjacent_intervals hh, ha0, han]
        _ = log 2 := by
              rw [integral_one_div_of_pos (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 6)]
              norm_num
    dsimp [L]
    rw [sum_add_distrib, ← mul_sum, hlogtel] at hsum
    rw [htel, ha0, han] at hsum
    have hlog2 : log (2 : ℝ) ≤ 1 := by have := log_two_lt_d9; linarith
    have herr := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2 * ε by positivity)
    nlinarith
  have hnear := hlim.eventually (gt_mem_nhds (show L < L + η / 2 by linarith))
  filter_upwards [hnear] with N hN
  have hpart := sum_short_blocks (s N) (t N) (fun q => φ (t N q) * w N q) a ha n
  have hwhole : (s N).filter (fun q => a 0 ≤ t N q ∧ t N q < a n) = s N := by
    apply filter_eq_self.mpr
    intro q hq
    simpa only [ha0, han] using ht N q hq
  rw [hwhole] at hpart
  rw [← hpart]
  have hle : (∑ i ∈ range n, ∑ q ∈ (s N).filter
      (fun q => a i ≤ t N q ∧ t N q < a (i + 1)), φ (t N q) * w N q) ≤
      ∑ i ∈ range n, (φ (a i) + ε) * ∑ q ∈ (s N).filter
      (fun q => a i ≤ t N q ∧ t N q < a (i + 1)), w N q := by
    apply sum_le_sum
    intro i hi
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    have hh := (mem_filter.mp hq).2
    have hosc' := (abs_lt.mp (hosc i (mem_range.mp hi) (t N q) ⟨hh.1, hh.2.le⟩)).1
    exact mul_le_mul_of_nonneg_right (by linarith) (hw N q (mem_filter.mp hq).1)
  dsimp [ε] at *
  linarith

/-- Derived second order local logarithm bound for the product on p. 61. -/
lemma log_odd_factor_second_order {p : ℝ} (hp : 3 ≤ p) :
    -(2 / p) - 8 / (p * (p - 1)) ≤ log ((p - 2) / p) := by
  have hp0 : 0 < p := by linarith
  have hm0 : 0 < p - 2 := by linarith
  have hm1 : 0 < p - 1 := by linarith
  have h := LeanLab.AlmostPrimes.DDLemma21.neg_log_one_sub_two_div hp
  have he : 1 - 2 / p = (p - 2) / p := by rw [sub_div, div_self hp0.ne']
  rw [he] at h
  have hcorr : 2 / (p * (p - 2)) ≤ 8 / (p * (p - 1)) := by
    rw [div_le_div_iff₀ (mul_pos hp0 hm0) (mul_pos hp0 hm1)]
    nlinarith [mul_nonneg hp0.le (show 0 ≤ p - 3 by linarith)]
  linarith

/-- Derived split of prime divisors at log N for the product bound on p. 61. -/
lemma prime_factor_recip_logloglog {N : ℕ} (hN : 2 ≤ N) (hL : 2 ≤ log (N : ℝ)) :
    ∑ p ∈ N.primeFactors, (1 : ℝ) / p ≤ log (log (log N)) + 7 + 1 / log 2 := by
  have hL0 : 0 < log (N : ℝ) := by linarith
  let S := N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ log N)
  let T := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ log N)
  have hsplit : N.primeFactors = S ∪ T := (filter_union_filter_not_eq _ _).symm
  have hS : ∑ p ∈ S, (1 : ℝ) / p ≤ log (log (log N)) + 7 := by
    have hsub : S ⊆ Nat.primesLE ⌊log (N : ℝ)⌋₊ := by
      intro p hp
      obtain ⟨hpN, hpL⟩ := mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hpN
      have hfloor : p ≤ ⌊log (N : ℝ)⌋₊ := Nat.le_floor hpL
      exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
    have hh := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
      show (0 : ℝ) ≤ 1 / p from by positivity)
    have hm := LeanLab.AlmostPrimes.Decomp1528b.sum_recip_le_explicit hL
    linarith
  have hT : ∑ p ∈ T, (1 : ℝ) / p ≤ 1 / log 2 := by
    calc ∑ p ∈ T, (1 : ℝ) / p ≤ ∑ p ∈ T, (1 : ℝ) / log N := by
          apply sum_le_sum
          intro p hp
          have hpL : log (N : ℝ) < p := lt_of_not_ge (mem_filter.mp hp).2
          exact div_le_div_of_nonneg_left (by norm_num) hL0 hpL.le
      _ = (T.card : ℝ) / log N := by simp [div_eq_mul_inv]
      _ ≤ (N.primeFactors.card : ℝ) / log N := by
          apply div_le_div_of_nonneg_right _ hL0.le
          have hcard : T.card ≤ N.primeFactors.card := card_le_card (filter_subset _ _)
          exact_mod_cast hcard
      _ ≤ (log (N : ℝ) / log 2) / log N := by
          apply div_le_div_of_nonneg_right _ hL0.le
          rw [le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))]
          exact LeanLab.HeathBrown1985.card_primeFactors_mul_log_two_le N (by omega)
      _ = 1 / log 2 := by field_simp [hL0.ne', (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rw [hsplit, sum_union (disjoint_filter_filter_not _ _ _)]
  linarith

/-- Derived summable correction for the logarithm product bound on p. 61. -/
lemma prime_factor_second_order_sum (N : ℕ) :
    ∑ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) / (p * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : N.primeFactors.filter (2 < ·) ⊆ (Ioc 1 N).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpN, hp2⟩ := mem_filter.mp hp
    have hp' := Nat.prime_of_mem_primeFactors hpN
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, Nat.le_of_mem_primeFactors hpN⟩, hp'⟩
  have hsum : (∑ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) / (p * ((p : ℝ) - 1))) ≤
      ∑ p ∈ (Ioc 1 N).filter Nat.Prime, (1 : ℝ) / (p * ((p : ℝ) - 1)) := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp2 := (mem_filter.mp hp).2.two_le
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg p) (by linarith))
  exact hsum.trans (by simpa using
    LeanLab.AlmostPrimes.Decomp1528b.sum_inv_pp1_tail 1 N (by norm_num))

/-- The inverse square log log product lower bound asserted on p. 61.
This proof uses only the proved elementary Mertens bounds, with no exact product constant. -/
theorem Q_loglog_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c / (log (log N)) ^ 2 < Q N := by
  let C : ℝ := 22 + 2 / log 2
  refine ⟨exp (-C) / 2, by positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop 3] with N hN hL
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hLL0 : 0 < log (log (N : ℝ)) := log_pos (by linarith)
  have hQ0 := (Q_bounds N).1
  have hprod : log (Q N) =
      ∑ p ∈ N.primeFactors.filter (2 < ·), log (((p : ℝ) - 2) / p) := by
    unfold Q
    apply log_prod
    intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2
    exact (div_pos (by linarith) (by linarith)).ne'
  have hlocal := sum_le_sum (s := N.primeFactors.filter (2 < ·)) (fun p hp =>
    log_odd_factor_second_order (p := (p : ℝ))
      (by exact_mod_cast (show 3 ≤ p from (mem_filter.mp hp).2)))
  have hsub : ∑ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) / p ≤
      ∑ p ∈ N.primeFactors, (1 : ℝ) / p := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro p _ _
    positivity
  have hrecip := prime_factor_recip_logloglog hN (by linarith)
  have hcorr := prime_factor_second_order_sum N
  have hsumid : (∑ p ∈ N.primeFactors.filter (2 < ·),
      (-(2 / (p : ℝ)) - 8 / ((p : ℝ) * ((p : ℝ) - 1)))) =
      -2 * (∑ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) / p) -
      8 * (∑ p ∈ N.primeFactors.filter (2 < ·), (1 : ℝ) / (p * ((p : ℝ) - 1))) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [hsumid, ← hprod] at hlocal
  have hlow : -C - 2 * log (log (log N)) ≤ log (Q N) := by
    dsimp [C]
    rw [show (2 : ℝ) / log 2 = 2 * (1 / log 2) by ring]
    linarith
  have hkey : exp (-C) ≤ Q N * (log (log N)) ^ 2 := by
    rw [← log_le_log_iff (exp_pos _) (mul_pos hQ0 (pow_pos hLL0 2)),
      log_exp, log_mul hQ0.ne' (pow_pos hLL0 2).ne', log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [div_lt_iff₀ (pow_pos hLL0 2)]
  have := exp_pos (-C)
  linarith

/-! ### Leaves -/

/-- LEAF. Unit U-1544. The prime sum to integral step on p. 65, "argue just as in [6, §5]":
for φ continuous on [3, 6] and η > 0, for all large N,
Σ_{N^{1/6} < q ≤ N^{1/3}} φ(log N/log q)/q ≤ ∫_3^6 φ(u)/u du + η.
Route: uniform continuity of φ, cut [3, 6] into short blocks, and on each block
Σ_{N^{1/u₂} < q ≤ N^{1/u₁}} 1/q = log(u₂/u₁) + O(1/log N) by `Decomp1528b.mertens2_block`. -/
theorem prime_sum_integral (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 3 6)) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      ∑ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
          φ (log N / log q) / q ≤ (∫ u in (3 : ℝ)..6, φ u / u) + η := by
  have h := continuous_test_of_blocks
    (fun N => (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N))
    (fun N q => log N / log q) (fun _ q => (1 : ℝ) / q)
    (fun _ _ _ => by positivity)
    (fun N q hq => by
      obtain ⟨hp, h6, h3⟩ := (mem_filter.mp hq).2
      have hN : 2 ≤ N := hp.two_le.trans ((Nat.le_self_pow (by norm_num : 3 ≠ 0) q).trans h3)
      exact (prime_log_window hN hp).mp ⟨h6, h3⟩)
    (fun _ _ ha hab hb => prime_block_tendsto ha hab hb) φ hφ hη
  simpa only [div_eq_mul_inv, one_mul] using h

/-- LEAF. Unit U-1544. B_N = 2^{ν(N)} = O(N^δ) for every δ > 0, used on p. 63 for
max_{d ≤ cN²} |R(d)| = O(N^ε) and on p. 65 for B_N N^{1-2ε} = o(φ(N)/log³ N). Route:
2^{ν(N)} ≤ τ(N) and the lab's PROVED `HeathBrown1985.card_divisors_le_rpow`. -/
theorem two_pow_omega_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (2 : ℝ) ^ ω N ≤ C * (N : ℝ) ^ δ := by
  exact Decomp1544a.two_pow_omega_le hδ

/-- LEAF. Unit U-1544. C_N > c (log log N)^{-2}, p. 61, in the form used for the relative error
of W_q on p. 64: for every c > 0, eventually c (1 + log N) √(log N) ≤ Q(N) log² N, where
C_N = T Q(N)/8. True since Q(N) = ∏_{p ∣ N, p > 2} (1 - 2/p) ≫ (log log N)^{-2}. -/
theorem Q_large {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, c * (1 + log N) * √(log N) ≤ Q N * (log N) ^ 2 := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop 1,
    hloglog.eventually_ge_atTop
      (4 * (10 * (3 ^ 40 : ℝ) + 22 + log c + log 2))] with N hN hL hLL
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hQ := (Q_bounds N).1
  have hsqrt : 0 < √(log (N : ℝ)) := sqrt_pos.mpr hL0
  apply (log_le_log_iff (mul_pos (mul_pos hc (by linarith)) hsqrt)
    (mul_pos hQ (pow_pos hL0 2))).mp
  rw [log_mul (mul_pos hc (by linarith)).ne' hsqrt.ne',
    log_mul hc.ne' (by linarith : 1 + log (N : ℝ) ≠ 0),
    log_sqrt hL0.le, log_mul hQ.ne' (pow_pos hL0 2).ne', log_pow]
  have hplus : log (1 + log (N : ℝ)) ≤ log 2 + log (log (N : ℝ)) := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) hL0.ne']
    exact log_le_log (by linarith) (by linarith)
  have hlow := log_Q_lower hN
  dsimp only [Function.comp_apply] at hLL
  norm_num only [Nat.cast_ofNat] at *
  linarith

/-- LEAF. Unit U-1544. Powers of log N are o(N^α): for α > 0 and η > 0, eventually
(1 + log N)^{10} ≤ η N^α. Used for the remainders on p. 65. Route: Mathlib
`isLittleO_log_rpow_rpow_atTop`. -/
theorem logpow_le_rpow {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 + log N) ^ 10 ≤ η * (N : ℝ) ^ α := by
  have H0 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x) ^ (10 : ℝ)) (fun x : ℝ ↦ x ^ α) := by
    exact isLittleO_log_rpow_rpow_atTop 10 hα
  have H1 : (fun x : ℝ ↦ (log x) ^ (10 : ℝ)) =ᶠ[atTop] (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (rpow_natCast (log x) 10)
  have H2 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) (fun x : ℝ ↦ x ^ α) := by
    exact H0.congr' H1 (EventuallyEq.refl atTop _)
  have H3 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ 1 + log x) (fun x : ℝ ↦ log x) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hlog : 1 ≤ log x := by
      have := Real.log_le_log (Real.exp_pos 1) hx
      rw [Real.log_exp] at this
      exact this
    have hlog_pos : 0 ≤ log x := by linarith
    have h_pos : 0 ≤ 1 + log x := by linarith
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg h_pos, abs_of_nonneg hlog_pos]
    linarith
  have H4 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (1 + log x) ^ (10 : ℕ)) (fun x : ℝ ↦ (log x) ^ (10 : ℕ)) := by
    exact H3.pow 10
  have H5 : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 + log x) ^ (10 : ℕ)) (fun x : ℝ ↦ x ^ α) := by
    exact H4.trans_isLittleO H2
  have H6 := H5.bound hη
  have H7 := tendsto_natCast_atTop_atTop.eventually H6
  filter_upwards [H7, eventually_ge_atTop 1] with N hN hN1
  have hN_real_pos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hc : 0 ≤ (1 + log (N : ℝ)) ^ (10 : ℕ) := by positivity
  rw [norm_eq_abs, abs_of_nonneg hc, norm_eq_abs, abs_of_nonneg (rpow_nonneg hN_real_pos α)] at hN
  exact hN

/-! ### Assemblies -/

/-- The remainders of p. 65 are negligible: for ε, η > 0, eventually
2^{ν(N)+1} N^{1-2ε} (1 + log N)⁷ ≤ η φ(N)/log² N. Assembly, CONDITIONAL ON
`two_pow_omega_le` and `logpow_le_rpow`, with the lab's PROVED `S3Small.le_totient_mul_log`. -/
theorem remainder_small {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 7) ≤
      η * (N.totient : ℝ) / (log N) ^ 2 := by
  obtain ⟨C, hC, hω⟩ := two_pow_omega_le hε
  set c0 : ℝ := exp 1 * (1 + 1 / log 2) with hc0
  have hc0p : 0 < c0 := by
    have : 0 < log (2 : ℝ) := log_pos (by norm_num); positivity
  have h2Cc : 0 < 2 * C * c0 := mul_pos (mul_pos two_pos hC) hc0p
  filter_upwards [logpow_le_rpow hε (div_pos hη h2Cc),
    eventually_ge_atTop 3] with N hlog hN3
  have hN1 : 1 ≤ N := by omega
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  set LN := log (N : ℝ) with hLN
  have hLN1 : 1 ≤ LN := by
    rw [hLN, ← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have htot := S3Small.le_totient_mul_log hN1 hLN1
  rw [← hc0, ← hLN] at htot
  have hφ0 : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr hN1
  have hωN := hω N hN1
  -- LHS ≤ 2 C N^{1-ε} (1+LN)^7
  have hsplit : (N : ℝ) ^ ε * (N : ℝ) ^ (1 - 2 * ε) = (N : ℝ) ^ (1 - ε) := by
    rw [← rpow_add hN0]; ring_nf
  have hP7 : 0 ≤ (1 + LN) ^ 7 := pow_nonneg (by linarith) 7
  have hL1 : (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 7) ≤
      2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) := by
    rw [pow_succ, ← hsplit]
    have := mul_le_mul_of_nonneg_right hωN
      (show 0 ≤ 2 * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 7) from
        mul_nonneg two_pos.le (mul_nonneg (rpow_nonneg hN0.le _) hP7))
    linarith
  -- RHS ≥ η N / (c0 LN³)
  have hR : η * (N : ℝ) / (c0 * LN ^ 3) ≤ η * (N.totient : ℝ) / LN ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hc0p (pow_pos (by linarith) 3)) (pow_pos (by linarith) 2)]
    have := mul_le_mul_of_nonneg_left htot (mul_nonneg hη.le (sq_nonneg LN))
    linarith
  refine hL1.trans (le_trans ?_ hR)
  rw [le_div_iff₀ (mul_pos hc0p (pow_pos (by linarith) 3))]
  have hL3 : LN ^ 3 ≤ (1 + LN) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hkey : 2 * C * c0 * (1 + LN) ^ 10 ≤ η * (N : ℝ) ^ ε := by
    have := mul_le_mul_of_nonneg_left hlog h2Cc.le
    rw [show 2 * C * c0 * (η / (2 * C * c0) * (N : ℝ) ^ ε) = η * (N : ℝ) ^ ε by
      field_simp] at this
    exact this
  have hNe : 0 < (N : ℝ) ^ (1 - ε) := rpow_pos_of_pos hN0 _
  have hA0 : 0 ≤ 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 :=
    mul_nonneg (mul_nonneg (mul_pos two_pos hC).le (mul_nonneg hNe.le hP7)) hc0p.le
  calc 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * (c0 * LN ^ 3)
      = 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 * LN ^ 3 := by ring
    _ ≤ 2 * C * ((N : ℝ) ^ (1 - ε) * (1 + LN) ^ 7) * c0 * (1 + LN) ^ 3 :=
        mul_le_mul_of_nonneg_left hL3 hA0
    _ = (N : ℝ) ^ (1 - ε) * (2 * C * c0 * (1 + LN) ^ 10) := by ring
    _ ≤ (N : ℝ) ^ (1 - ε) * (η * (N : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hkey hNe.le
    _ = η * ((N : ℝ) ^ (1 - ε) * (N : ℝ) ^ ε) := by ring
    _ = η * N := by rw [← rpow_add hN0, show 1 - ε + ε = (1 : ℝ) by ring, rpow_one]

/-- W_q with relative error, p. 64: for δ > 0, eventually for even N and 1 ≤ a ≤ 3,
W_q(N^{a/6}) ≥ (1 - δ) ((2a - 1)² - 2a² log a)/36 · C_N log² N. Assembly, CONDITIONAL ON
`Q_large` and the leaves of `Wq_lower`. -/
theorem Wq_relative {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ a : ℝ, 1 ≤ a → a ≤ 3 →
      (1 - δ) * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) ≤ Wq N ((N : ℝ) ^ (a / 6)) := by
  obtain ⟨Cw, hCw, hW⟩ := Wq_lower
  have hδ' : δ ≠ 0 := hδ.ne'
  filter_upwards [Q_large (c := 288 * Cw / δ) (div_pos (by linarith) hδ), eventually_ge_atTop 64]
    with N hQ hN64 hN a ha1 ha3
  have hWa := hW N hN hN64 a ha1 ha3
  have hqa : 1 ≤ TogashiUchiyama.q a := TogashiUchiyamaEpsilon.q_ge_one ⟨ha1, ha3⟩
  have hT := one_le_Ttwin
  have hQ0 := (Q_bounds N).1
  have hL : 0 ≤ (log N) ^ 2 := sq_nonneg _
  have hCK : Q N / 8 ≤ CK N := by
    simp only [CK, Cpaper]
    have : Q N ≤ Ttwin * Q N := by nlinarith
    linarith
  -- δ · (qa/36) CK L² ≥ δ/288 · Q L² ≥ Cw (1 + L) √L
  have h1 : Cw * (1 + log N) * √(log N) ≤ δ / 288 * (Q N * (log N) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hQ (show 0 ≤ δ / 288 by linarith)
    calc Cw * (1 + log N) * √(log N) = δ / 288 * (288 * Cw / δ * (1 + log N) * √(log N)) := by
          field_simp
      _ ≤ _ := this
  have h2 : δ / 288 * (Q N * (log N) ^ 2) ≤
      δ * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) := by
    have hA : Q N / 8 * (log N) ^ 2 ≤ TogashiUchiyama.q a * CK N * (log N) ^ 2 := by
      have : Q N / 8 ≤ TogashiUchiyama.q a * CK N := by
        have hCK0 : 0 ≤ CK N := CK_nonneg N
        nlinarith [mul_le_mul_of_nonneg_right hqa hCK0]
      exact mul_le_mul_of_nonneg_right this hL
    have := mul_le_mul_of_nonneg_left hA (show 0 ≤ δ / 36 by linarith)
    calc δ / 288 * (Q N * (log N) ^ 2) = δ / 36 * (Q N / 8 * (log N) ^ 2) := by ring
      _ ≤ δ / 36 * (TogashiUchiyama.q a * CK N * (log N) ^ 2) := this
      _ = _ := by ring
  linarith

/-- The per q bound of p. 65: for q ∈ Qset N, N even, N ≥ 64, given the relative W_q bound,
S(q) ≤ M C_ε(t_q)/(q(1 - δ)) + 2^{ν(N)+1} N^{1-2ε} (1 + log N)⁶/q, with
M = A_N φ(N)/log² N and t_q = log N/log q. Assembly from `Sq_le_selberg`,
CONDITIONAL ON its leaves. -/
theorem Sq_le_main {ε δ : ℝ} (hε0 : 0 < ε) (hε30 : ε < 1 / 30) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    {N q : ℕ} (hN : Even N) (hN64 : 64 ≤ N) (hq : q ∈ Qset N)
    (hW : ∀ a : ℝ, 1 ≤ a → a ≤ 3 →
      (1 - δ) * (TogashiUchiyama.q a / 36 * CK N * (log N) ^ 2) ≤ Wq N ((N : ℝ) ^ (a / 6))) :
    ((Sq N q).card : ℝ) ≤ M Ttwin N * Ceps ε (log N / log q) / q / (1 - δ) +
      (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 6) / q := by
  have hqm := mem_filter.mp hq
  obtain ⟨hqp, hq6, hq3, _⟩ := hqm.2
  have hNR : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by omega
  set LN := log (N : ℝ) with hLN
  have hLN0 : 0 < LN := log_pos (by linarith)
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hlq : 0 < log (q : ℝ) := log_pos (by linarith)
  have h3 : 3 * log (q : ℝ) ≤ LN := by
    have : ((q ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hq3
    have := log_le_log (by exact_mod_cast pow_pos hqp.pos 3) this
    rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
  have h6 : LN < 6 * log (q : ℝ) := by
    have : (N : ℝ) < ((q ^ 6 : ℕ) : ℝ) := by exact_mod_cast hq6
    have := log_lt_log hN0 this
    rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
  set t := LN / log (q : ℝ) with ht
  have ht3 : 3 ≤ t := by rw [ht, le_div_iff₀ hlq]; linarith
  have ht6 : t ≤ 6 := by rw [ht, div_le_iff₀ hlq]; linarith
  have hεE : ε ∈ TogashiUchiyamaEpsilon.E := ⟨hε0.le, hε30.le⟩
  have hA := TogashiUchiyamaEpsilon.A_range hεE ⟨ht3, ht6⟩
  obtain ⟨a, ha⟩ : ∃ a, a = TogashiUchiyamaEpsilon.A ε t := ⟨_, rfl⟩
  have hA1' : 1 < 3 * (1 - 2 * ε - 1 / t) := hA.1
  have ha1 : 1 ≤ a := by rw [ha]; exact hA.1.le
  have ha3 : a ≤ 3 := by rw [ha]; exact hA.2
  have hinvt : 1 / t = log (q : ℝ) / LN := by rw [ht, one_div_div]
  -- the level
  set w := (N : ℝ) ^ (a / 6) with hw
  have hw1 : 1 ≤ w := one_le_rpow (by linarith) (by linarith)
  have hexp : a / 6 * ((2 : ℕ) : ℝ) = 1 - 2 * ε - log (q : ℝ) / LN := by
    rw [ha, TogashiUchiyamaEpsilon.A, hinvt]; push_cast; ring
  have hw2 : w ^ 2 = (N : ℝ) ^ (1 - 2 * ε) / q := by
    rw [hw, ← rpow_natCast, ← rpow_mul hN0.le, hexp, rpow_def_of_pos hN0, rpow_def_of_pos hN0,
      ← hLN, show LN * (1 - 2 * ε - log (q : ℝ) / LN) = LN * (1 - 2 * ε) - log (q : ℝ) by
        field_simp, exp_sub, exp_log hq0]
  have hlw2 : log (w ^ 2) ≤ LN := by
    rw [hw2, log_div (rpow_pos_of_pos hN0 _).ne' hq0.ne', log_rpow hN0, ← hLN]
    nlinarith
  have hlw20 : 0 ≤ log (w ^ 2) := log_nonneg (by nlinarith)
  have hS := Sq_le_selberg hN hN1 hq hw1
  -- the main term
  have hqa : 1 ≤ TogashiUchiyama.q a := TogashiUchiyamaEpsilon.q_ge_one ⟨ha1, ha3⟩
  have hT := one_le_Ttwin
  have hQ0 := (Q_bounds N).1
  have hCK0 : 0 < CK N := by
    simp only [CK, Cpaper]; have := mul_pos (by linarith : (0:ℝ) < Ttwin) hQ0; linarith
  set V := TogashiUchiyama.q a / 36 * CK N * LN ^ 2 with hV
  have hV0 : 0 < V := by
    rw [hV]
    exact mul_pos (mul_pos (div_pos (by linarith) (by norm_num)) hCK0) (pow_pos hLN0 2)
  have hWa := hW a ha1 ha3
  have hδ1 : 0 < 1 - δ := by linarith
  have hWpos : 0 < (1 - δ) * V := mul_pos hδ1 hV0
  have hφ0 : (0 : ℝ) ≤ N.totient := Nat.cast_nonneg _
  have hmain1 : 2 * (N.totient : ℝ) / (q * Wq N w) ≤ 2 * (N.totient : ℝ) / (q * ((1 - δ) * V)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hq0 hWpos)
      (mul_le_mul_of_nonneg_left hWa hq0.le)
  have hCeps : Ceps ε t = TogashiUchiyamaEpsilon.K / TogashiUchiyama.q a := by
    rw [ha]
    simp only [Ceps, D, TogashiUchiyamaEpsilon.K, TogashiUchiyamaEpsilon.A]
    rw [if_neg (not_le.mpr hA1')]
  have hid : 2 * (N.totient : ℝ) / (q * ((1 - δ) * V)) =
      M Ttwin N * Ceps ε t / q / (1 - δ) := by
    rw [hCeps]
    simp only [M, Apaper, hV, TogashiUchiyamaEpsilon.K]
    have : CK N = Cpaper Ttwin N := rfl
    rw [← this, ← hLN]
    have he : 0 < exp (2 * eulerMascheroniConstant) := exp_pos _
    have hqa0 : 0 < TogashiUchiyama.q a := by linarith
    field_simp
    ring
  -- the remainder
  have hp6 : (1 + log (w ^ 2)) ^ 6 ≤ (1 + LN) ^ 6 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 6
  have hrem : (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6) ≤
      (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + LN) ^ 6) / q := by
    calc (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + log (w ^ 2)) ^ 6)
        ≤ (2 : ℝ) ^ (ω N + 1) * (w ^ 2 * (1 + LN) ^ 6) := by gcongr
      _ = _ := by rw [hw2]; ring
  rw [hid] at hmain1
  linarith

/-- **Section 3 summed upper sieve bound, `UpperSieveInput`**, pp. 63 to 65: for every
0 < ε < 1/30, eventually for even N,
Σ_{z<q≤z₁, (q, N) = 1} S(q) ≤ I(ε) A_N φ(N)/log² N + 3ε A_N φ(N)/log² N,
with T = `Ttwin` the true constant of p. 61. Assembly, CONDITIONAL ON the leaves of
Decomp1544a, Decomp1544b, Decomp1544c and the Decomp1528 leaves behind `mertens1_abs` and
`mertens2_block`. With `TogashiUchiyamaScale.section5_of_two_sieve_inputs` the main theorem of
P0072 is then CONDITIONAL ON Lemma 4 and these leaves only. -/
theorem upperSieveInput_of_leaves {ε : ℝ} (hε0 : 0 < ε) (hε30 : ε < 1 / 30) :
    UpperSieveInput Ttwin ε := by
  set I := TogashiUchiyamaEpsilon.I ε with hI
  set δ := min (1 / 2) (ε / (4 * (|I| + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε0 (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ * (4 * (|I| + 1)) ≤ ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / (4 * (|I| + 1)))
    rw [← hδdef] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hT := one_le_Ttwin
  have hTpos : 0 < Ttwin := by linarith
  have hεE : ε ∈ TogashiUchiyamaEpsilon.E := ⟨hε0.le, hε30.le⟩
  have hcont : ContinuousOn (Ceps ε) (Set.Icc 3 6) := by
    have h := (TogashiUchiyamaEpsilon.integrand_continuousOn hεE).mul continuousOn_id
    refine h.congr fun u hu => ?_
    have : u ≠ 0 := by linarith [hu.1]
    show Ceps ε u = Ceps ε u / u * u
    field_simp
  obtain ⟨Ch, hCh0, hCh⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ m ∈ Ioc 0 N, invW m ≤ 3 * (1 + log N) := by
    refine ⟨0, le_rfl, fun N hN => ?_⟩
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h := (abs_le.mp (harmonic_asymp hNR)).2
    rw [Nat.floor_natCast] at h
    have hγ := eulerMascheroniConstant_lt_two_thirds
    have h2 : 2 / (N : ℝ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have := log_nonneg hNR
    linarith
  filter_upwards [Wq_relative hδ0, prime_sum_integral (Ceps ε) hcont (show 0 < ε / 2 by linarith),
    remainder_small hε0 (div_pos (mul_pos hε0 (a_pos hTpos)) three_pos),
    eventually_ge_atTop 64] with N hWr hPS hR hN64 hN
  have hNR : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hM0 : 0 ≤ M Ttwin N := by
    have := M_lower hTpos N
    have : 0 ≤ a Ttwin * (N.totient : ℝ) / (log N) ^ 2 :=
      div_nonneg (mul_nonneg (a_pos hTpos).le (Nat.cast_nonneg _)) (sq_nonneg _)
    linarith
  have hδ1 : 0 < 1 - δ := by linarith
  -- per q
  have hper := fun q (hq : q ∈ Qset N) =>
    Sq_le_main hε0 hε30 hδ0 hδ2 hN hN64 hq (hWr hN)
  push_cast
  refine (sum_le_sum hper).trans ?_
  rw [sum_add_distrib]
  -- the C_ε sum
  set S := ∑ q ∈ Qset N, Ceps ε (log N / log q) / q with hSdef
  have hterm : ∀ q ∈ Qset N, M Ttwin N * Ceps ε (log N / log q) / q / (1 - δ) =
      M Ttwin N / (1 - δ) * (Ceps ε (log N / log q) / q) := by
    intro q _; field_simp
  rw [sum_congr rfl hterm, ← mul_sum]
  have hCpos : ∀ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
      0 ≤ Ceps ε (log N / log q) / q := by
    intro q hq
    obtain ⟨hqp, _, hq3⟩ := (mem_filter.mp hq).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
    have hlq : 0 < log (q : ℝ) := log_pos (by linarith)
    have h3 : 3 * log (q : ℝ) ≤ log N := by
      have : ((q ^ 3 : ℕ) : ℝ) ≤ N := by exact_mod_cast hq3
      have := log_le_log (by exact_mod_cast pow_pos hqp.pos 3) this
      rw [Nat.cast_pow, Real.log_pow] at this; push_cast at this; linarith
    have ht : 1 / (1 - 2 * ε) < log N / log q := by
      have h1 : 1 / (1 - 2 * ε) < 3 := by rw [div_lt_iff₀ (by linarith)]; linarith
      have h2 : 3 ≤ log N / log q := by rw [le_div_iff₀ hlq]; linarith
      linarith
    have := Ceps_pos hε0.le (by linarith) ht
    exact div_nonneg this.le (Nat.cast_nonneg q)
  have hS0 : 0 ≤ S := sum_nonneg fun q hq => hCpos q (by
    simp only [Qset, mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩)
  have hSle : S ≤ I + ε / 2 := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => hCpos q hq) hPS
    intro q hq
    simp only [Qset, mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1⟩
  -- the remainder sum
  set R := (2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 6) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hsub : ∑ q ∈ Qset N, ((q : ℝ))⁻¹ ≤ ∑ m ∈ Ioc 0 N, invW m := by
    simp only [invW_apply]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
    intro q hq
    simp only [Qset, mem_filter, mem_range] at hq
    exact mem_Ioc.mpr ⟨hq.2.1.pos, by omega⟩
  have hRsum : ∑ q ∈ Qset N, R / q ≤ R * (3 * (1 + log N)) := by
    calc ∑ q ∈ Qset N, R / q = R * ∑ q ∈ Qset N, ((q : ℝ))⁻¹ := by
          rw [mul_sum]; exact sum_congr rfl fun q _ => div_eq_mul_inv R q
      _ ≤ R * (3 * (1 + log N)) :=
          mul_le_mul_of_nonneg_left (hsub.trans (hCh N (by omega))) hR0
  have hRM : R * (3 * (1 + log N)) ≤ ε * M Ttwin N := by
    have h1 : R * (3 * (1 + log N)) =
        3 * ((2 : ℝ) ^ (ω N + 1) * ((N : ℝ) ^ (1 - 2 * ε) * (1 + log N) ^ 7)) := by
      rw [hRdef]; ring
    rw [h1]
    have h2 := M_lower hTpos N
    have h3 : 3 * (ε * a Ttwin / 3 * (N.totient : ℝ) / (log N) ^ 2) =
        ε * (a Ttwin * (N.totient : ℝ) / (log N) ^ 2) := by ring
    linarith [mul_le_mul_of_nonneg_left h2 hε0.le]
  -- combine
  have hfac : M Ttwin N / (1 - δ) * S ≤ M Ttwin N * (I + ε) := by
    have hinv : 1 / (1 - δ) ≤ 1 + 2 * δ := by
      rw [div_le_iff₀ hδ1]; nlinarith
    have hSI : S * (1 + 2 * δ) ≤ I + ε := by
      have hIabs : I ≤ |I| := le_abs_self I
      have hSb : S ≤ |I| + 1 := by linarith
      have h2δ : 2 * δ * S ≤ 2 * δ * (|I| + 1) :=
        mul_le_mul_of_nonneg_left hSb (by linarith)
      have : 2 * δ * S ≤ ε / 2 := by linarith
      linarith
    calc M Ttwin N / (1 - δ) * S = M Ttwin N * (S * (1 / (1 - δ))) := by ring
      _ ≤ M Ttwin N * (S * (1 + 2 * δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hS0) hM0
      _ ≤ M Ttwin N * (I + ε) := mul_le_mul_of_nonneg_left hSI hM0
  linarith [mul_nonneg hε0.le hM0]

/-- **P0072 main theorem from Lemma 4 alone, modulo the leaves.** There is ε, 0 < ε < 1/30,
such that if Lemma 4, `LowerSieveInput Ttwin ε`, holds then every large even N is n + (N - n)
with 1 < n < N - 1, (n, N) = 1, V(n) ≤ 3, V(N - n) ≤ 3. Assembly from
`TogashiUchiyamaScale.section5_of_two_sieve_inputs`, `TogashiUchiyamaEpsilon.exists_epsilon_interval`
and `upperSieveInput_of_leaves`; CONDITIONAL ON Lemma 4 and the leaves listed there. -/
theorem togashiUchiyama_of_lemma4 :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 30 ∧ (LowerSieveInput Ttwin ε →
      ∀ᶠ N : ℕ in atTop, Even N → ∃ n : ℕ,
        1 < n ∧ n < N - 1 ∧ n.Coprime N ∧ ArithmeticFunction.cardFactors n ≤ 3 ∧
          ArithmeticFunction.cardFactors (N - n) ≤ 3) := by
  obtain ⟨η, hη, hη30, hI⟩ := TogashiUchiyamaEpsilon.exists_epsilon_interval
  set ε : ℝ := min η (1 / 30000) with hεdef
  have hε : 0 < ε := lt_min hη (by norm_num)
  have hεη : ε ≤ η := min_le_left _ _
  have hεs : ε ≤ 1 / 30000 := min_le_right _ _
  have hε30 : ε < 1 / 30 := lt_of_le_of_lt hεη hη30
  refine ⟨ε, hε, hε30, fun hlow => ?_⟩
  have hT : 0 < Ttwin := lt_of_lt_of_le zero_lt_one one_le_Ttwin
  exact section5_of_two_sieve_inputs hT hε hεs (hI ε hε.le hεη) hlow
    (upperSieveInput_of_leaves hε hε30)

/-- Derived limit version of the continuous prime sum evaluation on p. 65.
The general continuous test function has no asserted uniform quantitative rate. -/
theorem prime_sum_integral_tendsto (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Set.Icc 3 6)) :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
        φ (log N / log q) / q) atTop (𝓝 (∫ u in (3 : ℝ)..6, φ u / u)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [prime_sum_integral φ hφ (show 0 < η / 2 by positivity),
    prime_sum_integral (fun u => -φ u) hφ.neg (show 0 < η / 2 by positivity)] with N hu hl
  simp only [neg_div, sum_neg_distrib, intervalIntegral.integral_neg] at hl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Lemma 5 at r equal to two, p. 65, with the paper's actual S₂ set and true normalization.
This is the eventual limiting form supplied by the proved summed upper sieve input. -/
theorem lemma5_S2_upper {ε : ℝ} (hε : 0 < ε) (hε30 : ε < 1 / 30) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((S2set N).card : ℝ) ≤ (TogashiUchiyamaEpsilon.I ε / 3 + ε) * M Ttwin N := by
  filter_upwards [upperSieveInput_of_leaves hε hε30] with N hN he
  have hdc : (3 : ℝ) * (S2set N).card ≤
      ((∑ q ∈ Qset N, (Sq N q).card : ℕ) : ℝ) := by
    exact_mod_cast S2_double_count N
  have hu := hN he
  nlinarith

/-- Lemma 5 on p. 65 for every integer r at least one, in eventual limiting form.
The count uses the indexed products and distinct primes in the paper's own window. -/
theorem lemma5_general_upper {ε : ℝ} (hε : 0 < ε) (hε30 : ε < 1 / 30)
    (r : ℕ) (_hr : 1 ≤ r) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (((S1set N).filter (fun n => r + 1 ≤
        ((Qset N).filter (fun q => q ∣ n * (N - n))).card)).card : ℝ) ≤
      ((TogashiUchiyamaEpsilon.I ε + 3 * ε) / ((r + 1 : ℕ) : ℝ)) * M Ttwin N := by
  filter_upwards [upperSieveInput_of_leaves hε hε30] with N hN he
  have hd := LeanLab.AlmostPrimeSums.TogashiUchiyamaCount.lemma5_double_count
    (S1set N) (Qset N) (fun n q => q ∣ n * (N - n)) r
  have hdc : ((r + 1 : ℕ) : ℝ) *
      (((S1set N).filter (fun n => r + 1 ≤
        ((Qset N).filter (fun q => q ∣ n * (N - n))).card)).card : ℝ) ≤
      ((∑ q ∈ Qset N, (Sq N q).card : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hr0 : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
  have hu := hN he
  calc _ ≤ ((∑ q ∈ Qset N, (Sq N q).card : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ) :=
        (le_div_iff₀ hr0).mpr (by nlinarith)
    _ ≤ (TogashiUchiyamaEpsilon.I ε * M Ttwin N + 3 * (ε * M Ttwin N)) /
        ((r + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hu hr0.le
    _ = _ := by ring

/-! ### Vacuity instances -/

/-- The hypotheses of `upperSieveInput_of_leaves` can hold: ε = 1/60. -/
theorem vacuity_c1 : (0 : ℝ) < 1 / 60 ∧ (1 / 60 : ℝ) < 1 / 30 := by norm_num

/-- The hypotheses of `Sq_le_main` can hold, apart from the W_q bound which `Wq_relative`
supplies eventually: N = 30030 is even, 30030 ≥ 64, and 17 ∈ Qset 30030; δ = 1/4. -/
theorem vacuity_c2 : Even 30030 ∧ 64 ≤ 30030 ∧ 17 ∈ Qset 30030 ∧ (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / 2 := by
  refine ⟨by decide, by norm_num, ?_, by norm_num, by norm_num⟩
  simp only [Qset, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Concrete positive exponent and positive integer for the omega growth bound on p. 63. -/
example : (0 : ℝ) < 1 ∧ 1 ≤ (1 : ℕ) := by norm_num

/-- Concrete local factor at the first odd prime for p. 61. -/
example : -(10 / (3 : ℝ)) ≤ log ((3 - 2) / 3) :=
  log_odd_factor_lower (by norm_num)

/-- Concrete positive modulus for the weak product bound on p. 61. -/
example : -(10 * (3 ^ 40 : ℝ) + 22) - (1 / 4 : ℝ) * log (log 2) ≤ log (Q 2) :=
  log_Q_lower (by norm_num)

/-- A nonempty prime window at N equal to 64 for the p. 65 change of variables. -/
example : 3 ≤ log (64 : ℝ) / log 3 ∧ log (64 : ℝ) / log 3 < 6 :=
  (prime_log_window (by norm_num : 2 ≤ 64) (by norm_num : Nat.Prime 3)).mp
    ⟨by norm_num, by norm_num⟩

/-- The full interval is a valid fixed short block for the p. 65 Mertens limit. -/
example : Tendsto (fun N : ℕ => ∑ q ∈
    ((range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N)).filter
      (fun q : ℕ => (3 : ℝ) ≤ log N / log q ∧ log N / log q < 6), (1 : ℝ) / q)
    atTop (𝓝 (log 2)) := by
  convert prime_block_tendsto (by norm_num : (3 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 6) using 1 <;> norm_num

/-- The p. 65 continuous test permits a negative constant function. -/
example : ∀ᶠ N : ℕ in atTop,
    ∑ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
      (-1 : ℝ) / q ≤ (∫ u in (3 : ℝ)..6, (-1 : ℝ) / u) + 1 :=
  prime_sum_integral (fun _ => -1) continuousOn_const (by norm_num)

/-- The relative product estimate has a positive coefficient instance. -/
example : ∀ᶠ N : ℕ in atTop,
    (1 : ℝ) * (1 + log N) * √(log N) ≤ Q N * (log N) ^ 2 :=
  Q_large (by norm_num)

/-- A monotone endpoint instance for the finite short block partition. -/
example : Monotone (fun i : ℕ => (i : ℝ)) := by
  intro i j h
  change (i : ℝ) ≤ (j : ℝ)
  exact_mod_cast h

/-- The first odd prime satisfies the second order local bound. -/
example : -(2 / (3 : ℝ)) - 8 / (3 * (3 - 1)) ≤ log ((3 - 2) / 3) :=
  log_odd_factor_second_order (by norm_num)

/-- A concrete modulus for the split at log N on p. 61. -/
example : 2 ≤ (64 : ℕ) ∧ 2 ≤ log (64 : ℝ) := by
  constructor
  · norm_num
  · rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
    have := log_two_gt_d9
    norm_num only [Nat.cast_ofNat]
    linarith

/-- The summable correction has a concrete odd prime instance. -/
example : ∑ p ∈ (3 : ℕ).primeFactors.filter (2 < ·),
    (1 : ℝ) / (p * ((p : ℝ) - 1)) ≤ 1 := prime_factor_second_order_sum 3

/-- The printed lower bound supplies a positive constant and a nonempty eventual range. -/
example : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, c / (log (log N)) ^ 2 < Q N := by
  obtain ⟨c, hc, h⟩ := Q_loglog_lower
  obtain ⟨N, hN⟩ := h.exists
  exact ⟨c, hc, N, hN⟩

/-- A negative continuous test function also has the two sided prime sum limit. -/
example : Tendsto (fun N : ℕ =>
    ∑ q ∈ (range (N + 1)).filter (fun q => q.Prime ∧ N < q ^ 6 ∧ q ^ 3 ≤ N),
      (-1 : ℝ) / q) atTop (𝓝 (∫ u in (3 : ℝ)..6, (-1 : ℝ) / u)) :=
  prime_sum_integral_tendsto (fun _ => -1) continuousOn_const

/-- Concrete parameter hypotheses for the general r form of Lemma 5. -/
example : 1 ≤ (2 : ℕ) ∧ (0 : ℝ) < 1 / 60 ∧ (1 / 60 : ℝ) < 1 / 30 := by norm_num

/-- A positive epsilon instance of the actual S₂ count bound. -/
example : ∀ᶠ N : ℕ in atTop, Even N →
    ((S2set N).card : ℝ) ≤ (TogashiUchiyamaEpsilon.I (1 / 60) / 3 + 1 / 60) * M Ttwin N :=
  lemma5_S2_upper (by norm_num) (by norm_num)

end LeanLab.AlmostPrimeSums.Decomp1544c
