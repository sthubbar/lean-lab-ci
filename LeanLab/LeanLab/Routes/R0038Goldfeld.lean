import Mathlib
import LeanLab.Routes.R0038

/-
# R-0038, T2 salvage: Goldfeld's count of p < N with a prime factor q of N - p above √N

Unit U-1407, PC run 20261021T1203Z-6472, track T2. AI-written Lean code, Claude. Checked only by
the Lean kernel. KNOWN mathematics: Goldfeld 1969, with Bombieri-Vinogradov. Not new, and not
progress on binary Goldbach, which is OPEN.

Target, plain mathematics: for every ε > 0 and every large N, at least (1/2 - ε) π(N) primes
p < N have a prime factor q of N - p with N < q².

Proof skeleton, every step below is a Lean statement in this file:

* `log_le_split`, PROVED: for 0 < n ≤ N, by Chebyshev's identity log n = Σ_{d ∣ n} Λ(d),
  log n ≤ Σ_{d ∣ n, d² ≤ N} Λ(d) + Σ_{d ∣ n, d² > N, d not prime} Λ(d) + log N · 1[n has a prime
  factor q with q² > N]; the last term is `R0038.sum_log_large_le`.
* `sumLog_le`, PROVED: summed over n = N - p, p < N prime,
  Σ_p log(N - p) ≤ Tsmall N + Tpp N + log N · #good N.
* `sumLog_ge`, PROVED: Σ_p log(N - p) ≥ S (log N - log T) - log N · N/T for every T ≥ 1,
  S = #{p < N prime}.
* `S_mul_log_ge`, PROVED: eventually N ≤ 2 S log N, from Mathlib's Chebyshev bound `pi_ge`.
* `goldfeld_of`, CONDITIONAL ON the two named inputs `SmallDivBound` and `PrimePowerTail`.
* `Tpp_le`, PROVED: Tpp N ≤ log N · N/M whenever 1 ≤ M and M⁶ ≤ N, since a proper prime power
  q^k > √N dividing n forces a square m² ∣ n with m⁶ > N.
* `primePowerTail`, PROVED: the named input `PrimePowerTail` holds unconditionally.
* `goldfeld_of_smallDiv`, CONDITIONAL ON `SmallDivBound` only.

What stays open here is `SmallDivBound`, the Bombieri-Vinogradov step. Three routes were weighed:
1. bvPi in the mirror of `tauSum_lower`: right route, but the PNTPort chain is not built in this
   workspace, and the step also needs Mertens for Λ(d)/φ(d), the prime number theorem comparison
   liD(N) against π(N), and the d ∣ N terms; not done in this session.
2. Brun-Titchmarsh alone for every d ≤ √N: the factor 2 gives about 2 log 2 · N > N for the small
   divisor mass, so the bound is useless for a positive proportion.
3. Counting all n ≤ N in place of n = N - p: gives N log √N, larger than π(N) log N by a log N
   factor, useless.
-/

namespace LeanLab.Routes.R0038Goldfeld

open ArithmeticFunction Finset Filter
open scoped Classical

/-- The primes p < N. -/
def P (N : ℕ) : Finset ℕ := (range N).filter Nat.Prime

/-- S N = #{p < N prime} = π(N - 1). -/
noncomputable def S (N : ℕ) : ℝ := ((P N).card : ℝ)

/-- The primes p < N such that N - p has a prime factor q with N < q². -/
noncomputable def good (N : ℕ) : Finset ℕ :=
  (P N).filter (fun p => ∃ q, q.Prime ∧ q ∣ N - p ∧ N < q * q)

/-- Tsmall N = Σ_{p < N} Σ_{d ∣ N - p, d² ≤ N} Λ(d) = Σ_{d ≤ √N} Λ(d) #{p < N : d ∣ N - p}. -/
noncomputable def Tsmall (N : ℕ) : ℝ :=
  ∑ p ∈ P N, ∑ d ∈ (N - p).divisors.filter (fun d => d * d ≤ N), vonMangoldt d

/-- Tpp N = Σ_{p < N} Σ_{d ∣ N - p, d² > N, d a prime power that is not prime} Λ(d). -/
noncomputable def Tpp (N : ℕ) : ℝ :=
  ∑ p ∈ P N, ∑ d ∈ (N - p).divisors.filter (fun d => N < d * d ∧ ¬ d.Prime), vonMangoldt d

/-- Chebyshev's identity split at √N, with Goldfeld's deterministic core for the primes above √N. -/
theorem log_le_split {n N : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) :
    Real.log n ≤ ∑ d ∈ n.divisors.filter (fun d => d * d ≤ N), vonMangoldt d
      + ∑ d ∈ n.divisors.filter (fun d => N < d * d ∧ ¬ d.Prime), vonMangoldt d
      + Real.log N * (if ∃ q, q.Prime ∧ q ∣ n ∧ N < q * q then 1 else 0) := by
  rw [← vonMangoldt_sum, ← sum_filter_add_sum_filter_not n.divisors (fun d => d * d ≤ N),
    ← sum_filter_add_sum_filter_not (n.divisors.filter (fun d => ¬ d * d ≤ N)) (fun d => d.Prime)]
  have e1 : (n.divisors.filter (fun d => ¬ d * d ≤ N)).filter (fun d => d.Prime) =
      (n.primeFactors).filter (fun q => N < q * q) := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.mem_primeFactors, not_le]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨h4, h1, h2⟩, h3⟩
    · rintro ⟨⟨h4, h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  have e2 : (n.divisors.filter (fun d => ¬ d * d ≤ N)).filter (fun d => ¬ d.Prime) =
      n.divisors.filter (fun d => N < d * d ∧ ¬ d.Prime) := by
    ext d
    simp only [mem_filter, not_le, and_assoc]
  rw [e1, e2]
  have hprime : ∑ q ∈ (n.primeFactors).filter (fun q => N < q * q), vonMangoldt q =
      ∑ q ∈ (n.primeFactors).filter (fun q => N < q * q), Real.log q := by
    refine sum_congr rfl (fun q hq => ?_)
    simp only [mem_filter, Nat.mem_primeFactors] at hq
    exact vonMangoldt_apply_prime hq.1.1
  have hcore := LeanLab.Routes.R0038.sum_log_large_le hn0 hnN
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hind : Real.log N * (((n.primeFactors).filter (fun q => N < q * q)).card : ℝ) ≤
      Real.log N * (if ∃ q, q.Prime ∧ q ∣ n ∧ N < q * q then 1 else 0) := by
    split_ifs with h
    · have := LeanLab.Routes.R0038.card_large_primeFactors_le_one hn0 hnN
      have : (((n.primeFactors).filter (fun q => N < q * q)).card : ℝ) ≤ 1 := by exact_mod_cast this
      nlinarith
    · have : (n.primeFactors).filter (fun q => N < q * q) = ∅ := by
        rw [filter_eq_empty_iff]
        intro q hq hqN
        rw [Nat.mem_primeFactors] at hq
        exact h ⟨q, hq.1, hq.2.1, hqN⟩
      rw [this]; simp
  rw [hprime]
  linarith

/-- Summed over n = N - p: Σ_{p < N} log(N - p) ≤ Tsmall N + Tpp N + log N · #good N. -/
theorem sumLog_le (N : ℕ) :
    ∑ p ∈ P N, Real.log ((N - p : ℕ) : ℝ) ≤ Tsmall N + Tpp N + Real.log N * ((good N).card : ℝ) := by
  have hcard : ((good N).card : ℝ) =
      ∑ p ∈ P N, (if ∃ q, q.Prime ∧ q ∣ N - p ∧ N < q * q then (1 : ℝ) else 0) := by
    unfold good
    rw [card_filter]; push_cast; rfl
  rw [hcard, mul_sum, Tsmall, Tpp, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_le_sum (fun p hp => ?_)
  simp only [P, mem_filter, mem_range] at hp
  exact log_le_split (by omega) (Nat.sub_le N p)

/-- Lower bound: Σ_{p < N} log(N - p) ≥ S (log N - log T) - log N · N/T, for every T ≥ 1. -/
theorem sumLog_ge (N : ℕ) (T : ℝ) (hT : 1 ≤ T) :
    S N * (Real.log N - Real.log T) - Real.log N * (N / T) ≤
      ∑ p ∈ P N, Real.log ((N - p : ℕ) : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set Bad := (P N).filter (fun p => ((N - p : ℕ) : ℝ) < N / T) with hBad
  have hper : ∀ p ∈ P N, Real.log N - Real.log T - Real.log N *
      (if ((N - p : ℕ) : ℝ) < N / T then 1 else 0) ≤ Real.log ((N - p : ℕ) : ℝ) := by
    intro p hp
    simp only [P, mem_filter, mem_range] at hp
    have hpos : (0 : ℝ) < ((N - p : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - p by omega)
    split_ifs with h
    · have := Real.log_natCast_nonneg (N - p); linarith
    · push Not at h
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have := Real.log_le_log (div_pos hNpos hT0) h
      rw [Real.log_div hNpos.ne' hT0.ne'] at this
      linarith
  have hsum := sum_le_sum hper
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum] at hsum
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hcnt : ∑ p ∈ P N, (if ((N - p : ℕ) : ℝ) < N / T then (1 : ℝ) else 0) ≤ N / T := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hinj : (Bad.card) ≤ (Icc 1 ⌊(N : ℝ) / T⌋₊).card := by
      refine card_le_card_of_injOn (fun p => N - p) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, hBad, mem_filter, P, mem_filter, mem_range] at hp
        rw [Finset.mem_coe, mem_Icc]
        have h1 := hp.1.1
        refine ⟨?_, Nat.le_floor hp.2.le⟩
        show 1 ≤ N - p
        omega
      · intro a ha b hb hab
        rw [Finset.mem_coe, hBad, mem_filter, P, mem_filter, mem_range] at ha hb
        have hab' : N - a = N - b := hab
        have h1 := ha.1.1
        have h2 := hb.1.1
        omega
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hinj
    calc (Bad.card : ℝ) ≤ (⌊(N : ℝ) / T⌋₊ : ℝ) := by exact_mod_cast hinj
      _ ≤ N / T := Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hT0.le)
  have : Real.log N * ∑ p ∈ P N, (if ((N - p : ℕ) : ℝ) < N / T then (1 : ℝ) else 0) ≤
      Real.log N * (N / T) := mul_le_mul_of_nonneg_left hcnt hlogN
  unfold S
  nlinarith

/-- log x ≤ c x for all large real x, from Mathlib's `isLittleO_log_id_atTop`. -/
theorem log_le_eps {c : ℝ} (hc : 0 < c) : ∃ a : ℝ, ∀ x ≥ a, Real.log x ≤ c * x := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp (Real.isLittleO_log_id_atTop.bound hc)
  refine ⟨max a 1, fun x hx => ?_⟩
  have h := ha x (le_of_max_le_left hx)
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos (show (0 : ℝ) < x by linarith)] at h
  exact (le_abs_self _).trans h

/-- π(N) ≤ S N + 1: the primes ≤ N are the primes < N and possibly N. -/
theorem primeCounting_le_S_add_one (N : ℕ) : (Nat.primeCounting N : ℝ) ≤ S N + 1 := by
  have h : Nat.primeCounting N = ((range (N + 1)).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have h2 : ((range (N + 1)).filter Nat.Prime).card ≤ (P N).card + 1 := by
    rw [range_add_one, filter_insert]
    split_ifs
    · exact card_insert_le _ _
    · exact Nat.le_succ _
  unfold S
  rw [h]
  exact_mod_cast h2

/-- Chebyshev, from Mathlib's `pi_ge`: eventually N ≤ 2 S(N) log N. -/
theorem S_mul_log_ge : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ 2 * S N * Real.log N := by
  obtain ⟨a, ha⟩ := log_le_eps (show (0 : ℝ) < 1 / 20 by norm_num)
  refine eventually_atTop.mpr ⟨⌈a⌉₊ + 30, fun N hN => ?_⟩
  have hNa : a ≤ (N : ℝ) := by
    have := Nat.le_ceil a
    have : ((⌈a⌉₊ + 30 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at this; linarith
  have hN30 : (30 : ℝ) ≤ N := by
    have : ((⌈a⌉₊ + 30 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at this; linarith [Nat.cast_nonneg (α := ℝ) ⌈a⌉₊]
  have hlogN := ha N hNa
  have hlogN1 := ha (N + 1) (by linarith)
  have hLpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge N
  rw [div_le_iff₀ hLpos] at hpi
  have hpiS := primeCounting_le_S_add_one N
  have hl2 := Real.log_two_gt_d9
  have : (Nat.primeCounting N : ℝ) * Real.log N ≤ (S N + 1) * Real.log N :=
    mul_le_mul_of_nonneg_right hpiS hLpos.le
  nlinarith

/-- **Named input 1, SmallDivBound.** Plain mathematics: for every ε > 0 and all large N,
Σ_{d ≤ √N} Λ(d) #{p < N prime : d ∣ N - p} ≤ (1/2 + ε) π(N - 1) log N.
This is the analytic heart of Goldfeld's argument: Bombieri-Vinogradov, the lab's `bvPi`, for
d ≤ √N/log^B N with Mertens Σ_{d ≤ x} Λ(d)/φ(d) ≤ log x + O(1) and the prime number theorem
liD(N) = π(N) + O(N/log^A N); Brun-Titchmarsh, the lab's `brunTitchmarsh_ap`, for the gap
√N/log^B N < d ≤ √N, contributing O(N log log N/log N). -/
def SmallDivBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Tsmall N ≤ (1 / 2 + ε) * S N * Real.log N

/-- **Named input 2, PrimePowerTail.** Plain mathematics: for every ε > 0 and all large N, the
proper prime powers d with d² > N contribute Σ_{p < N} Σ_{d ∣ N - p} Λ(d) ≤ ε π(N - 1) log N. -/
def PrimePowerTail : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, Tpp N ≤ ε * S N * Real.log N

/-- **Goldfeld's count, reduction.** CONDITIONAL ON `SmallDivBound` and `PrimePowerTail`: for every
ε > 0 and all large N, at least (1/2 - ε) π(N - 1) primes p < N have a prime factor q of N - p
with N < q². -/
theorem goldfeld_of (hS : SmallDivBound) (hP : PrimePowerTail) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 / 2 - ε) * S N ≤ ((good N).card : ℝ) := by
  intro ε hε
  set δ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨a, ha⟩ := log_le_eps (show (0 : ℝ) < δ / 2 by positivity)
  have hL : ∀ᶠ N : ℕ in atTop, max (max a 1) (2 / δ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hS δ hδ0, hP δ hδ0, S_mul_log_ge, hL] with N hs hpp hcheb hLN
  set L := Real.log N with hLdef
  have hLa : a ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLN
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLN
  have hL2 : 2 / δ ≤ L := le_trans (le_max_right _ _) hLN
  have hLpos : 0 < L := by linarith
  have hS0 : 0 ≤ S N := Nat.cast_nonneg _
  have hlogL := ha L hLa
  have hT : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hlow := sumLog_ge N (L ^ 2) hT
  have hup := sumLog_le N
  rw [← hLdef] at hlow hup
  have hlogT : Real.log (L ^ 2) = 2 * Real.log L := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogT] at hlow
  have hNL : L * ((N : ℝ) / L ^ 2) = (N : ℝ) / L := by field_simp
  rw [hNL] at hlow
  have h2δ : 2 ≤ δ * L := by rw [div_le_iff₀ hδ0] at hL2; linarith
  have hNdiv : (N : ℝ) / L ≤ δ * S N * L := by
    rw [div_le_iff₀ hLpos]
    have : 2 * S N * L ≤ δ * L * S N * L := by
      have := mul_le_mul_of_nonneg_right h2δ (mul_nonneg hS0 hLpos.le)
      nlinarith
    nlinarith
  have hlogLS : S N * (2 * Real.log L) ≤ S N * (δ * L) := by
    apply mul_le_mul_of_nonneg_left _ hS0; linarith
  have key : (1 / 2 - ε) * S N * L ≤ ((good N).card : ℝ) * L := by
    rw [hδ] at hs hpp hNdiv hlogLS; nlinarith
  exact le_of_mul_le_mul_right key hLpos

/-- A proper prime power d = q^k, k ≥ 2, with N < d² dividing n yields a square m² ∣ n with
N < m⁶: take m = q^⌊k/2⌋, since 6⌊k/2⌋ ≥ 2k for k ≥ 2. -/
theorem sq_dvd_of_proper_pp {n N d : ℕ} (hd : d ∣ n) (hpp : IsPrimePow d) (hnp : ¬ d.Prime)
    (hN : N < d * d) : ∃ m, m * m ∣ n ∧ N < m ^ 6 := by
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hpp
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    subst this; exact hnp (by simpa using hq)
  refine ⟨q ^ (k / 2), ?_, ?_⟩
  · rw [← pow_add]
    exact (pow_dvd_pow q (by omega)).trans hd
  · have h1 : q ^ k * q ^ k = q ^ (2 * k) := by rw [← pow_add]; ring_nf
    rw [h1] at hN
    rw [← pow_mul]
    exact lt_of_lt_of_le hN (Nat.pow_le_pow_right hq.pos (by omega))

/-- Per n: the proper prime powers d ∣ n with N < d² carry Λ-mass at most log N, and none unless
n has a square divisor m² with N < m⁶. -/
theorem pp_part_le {n N : ℕ} (hn0 : 0 < n) (hnN : n ≤ N) :
    ∑ d ∈ n.divisors.filter (fun d => N < d * d ∧ ¬ d.Prime), vonMangoldt d ≤
      Real.log N * (if ∃ m, m * m ∣ n ∧ N < m ^ 6 then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]
    calc _ ≤ ∑ d ∈ n.divisors, vonMangoldt d :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => vonMangoldt_nonneg)
      _ = Real.log n := vonMangoldt_sum
      _ ≤ Real.log N := Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnN)
  · rw [mul_zero]
    refine le_of_eq (sum_eq_zero (fun d hd => ?_))
    simp only [mem_filter, Nat.mem_divisors] at hd
    rw [vonMangoldt_apply, if_neg]
    intro hpp
    exact h (sq_dvd_of_proper_pp hd.1.1 hpp hd.2.2 hd.2.1)

/-- Σ_{m = M+1}^{K} 1/m² ≤ 1/M - 1/K for 1 ≤ M ≤ K. -/
theorem sum_inv_sq_tail (M : ℕ) (hM : 1 ≤ M) :
    ∀ K, M ≤ K → ∑ m ∈ Icc (M + 1) K, (1 : ℝ) / ((m : ℝ) * m) ≤ 1 / M - 1 / K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hMK ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (le_trans hM hMK)
    have hstep : (1 : ℝ) / (((K + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) ≤ 1 / K - 1 / ((K + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- The proper prime power tail, unconditional: for 1 ≤ M with M⁶ ≤ N,
Tpp N ≤ log N · N/M, by counting n ≤ N with a square divisor m² for some m > M. -/
theorem Tpp_le (N M : ℕ) (hM : 1 ≤ M) (hMN : M ^ 6 ≤ N) :
    Tpp N ≤ Real.log N * (N / M) := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set Bad := (P N).filter (fun p => ∃ m, m * m ∣ N - p ∧ N < m ^ 6) with hBad
  -- step 1: Tpp ≤ log N · #Bad
  have h1 : Tpp N ≤ Real.log N * (Bad.card : ℝ) := by
    have hcard : (Bad.card : ℝ) =
        ∑ p ∈ P N, (if ∃ m, m * m ∣ N - p ∧ N < m ^ 6 then (1 : ℝ) else 0) := by
      rw [hBad, card_filter]; push_cast; rfl
    rw [hcard, mul_sum, Tpp]
    refine sum_le_sum (fun p hp => ?_)
    simp only [P, mem_filter, mem_range] at hp
    exact pp_part_le (by omega) (Nat.sub_le N p)
  -- step 2: #Bad ≤ Σ_{M < m ≤ N} N/m²
  have hsub : Bad ⊆ (Icc (M + 1) N).biUnion
      (fun m => (P N).filter (fun p => m * m ∣ N - p)) := by
    intro p hp
    rw [hBad, mem_filter] at hp
    obtain ⟨hpP, m, hm, hmN⟩ := hp
    have hpN : p < N := by simp only [P, mem_filter, mem_range] at hpP; exact hpP.1
    rw [mem_biUnion]
    refine ⟨m, ?_, mem_filter.mpr ⟨hpP, hm⟩⟩
    rw [mem_Icc]
    constructor
    · by_contra hc
      have : m ≤ M := by omega
      have := Nat.pow_le_pow_left this 6
      omega
    · have hmm := Nat.le_of_dvd (by omega) hm
      have : m ≤ m * m := Nat.le_mul_self m
      omega
  have h2 : (Bad.card : ℝ) ≤ ∑ m ∈ Icc (M + 1) N, ((N / (m * m) : ℕ) : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    have h3 : ∀ m ∈ Icc (M + 1) N, ((P N).filter (fun p => m * m ∣ N - p)).card ≤ N / (m * m) := by
      intro m _
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      refine card_le_card_of_injOn (fun p => N - p) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, mem_filter, P, mem_filter, mem_range] at hp
        rw [Finset.mem_coe, mem_filter, mem_Ioc]
        have := hp.1.1
        exact ⟨⟨by show 0 < N - p; omega, by show N - p ≤ N; omega⟩, hp.2⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe, mem_filter, P, mem_filter, mem_range] at ha hb
        have hab' : N - a = N - b := hab
        have := ha.1.1
        have := hb.1.1
        omega
    exact_mod_cast this.trans (sum_le_sum h3)
  -- step 3: Σ_{M < m ≤ N} N/m² ≤ N/M
  have h4 : ∑ m ∈ Icc (M + 1) N, ((N / (m * m) : ℕ) : ℝ) ≤ N / M := by
    have hMN' : M ≤ N := le_trans (Nat.le_self_pow (by norm_num) M) hMN
    have ht := sum_inv_sq_tail M hM N hMN'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc ∑ m ∈ Icc (M + 1) N, ((N / (m * m) : ℕ) : ℝ)
        ≤ ∑ m ∈ Icc (M + 1) N, (N : ℝ) * (1 / ((m : ℝ) * m)) := by
          refine sum_le_sum (fun m _ => ?_)
          rw [mul_one_div]
          have := Nat.cast_div_le (α := ℝ) (m := N) (n := m * m)
          push_cast at this; exact this
      _ = (N : ℝ) * ∑ m ∈ Icc (M + 1) N, (1 / ((m : ℝ) * m)) := by rw [mul_sum]
      _ ≤ (N : ℝ) * (1 / M - 1 / N) := mul_le_mul_of_nonneg_left ht hN0.le
      _ ≤ (N : ℝ) * (1 / M) := by
          apply mul_le_mul_of_nonneg_left _ hN0.le
          have : (0 : ℝ) ≤ 1 / N := by positivity
          linarith
      _ = N / M := by ring
  calc Tpp N ≤ Real.log N * (Bad.card : ℝ) := h1
    _ ≤ Real.log N * (N / M) := mul_le_mul_of_nonneg_left (h2.trans h4) hlogN

/-- `PrimePowerTail` holds, unconditional: take M = ⌈c log N⌉ with c = 2/ε + 1, so M⁶ ≤ N for
large N, and Tpp N ≤ log N · N/M ≤ ε S log N by Chebyshev's N ≤ 2 S log N. -/
theorem primePowerTail : PrimePowerTail := by
  intro ε hε
  set c : ℝ := 2 / ε + 1 with hc
  have hc0 : 0 < c := by positivity
  have hcε : 2 ≤ ε * c := by
    rw [hc, mul_add, mul_div_cancel₀ _ hε.ne']; linarith
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    ((Real.isLittleO_pow_log_id_atTop (n := 6)).bound
      (show (0 : ℝ) < 1 / (c + 1) ^ 6 by positivity))
  have hNa : ∀ᶠ N : ℕ in atTop, max a 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hL : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hNa, hL, S_mul_log_ge] with N hN hL1 hcheb
  have hN1 : (1 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hbound := ha N (le_trans (le_max_left _ _) hN)
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (by positivity),
    abs_of_nonneg (by linarith)] at hbound
  set M := ⌈c * L⌉₊ with hMdef
  have hS0 : 0 ≤ S N := Nat.cast_nonneg _
  have hML : c * L ≤ M := Nat.le_ceil _
  have hMup : (M : ℝ) ≤ (c + 1) * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ c * L by positivity)
    rw [← hMdef] at this; nlinarith
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 < 2 / ε := by positivity
                         linarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by nlinarith
    exact_mod_cast this
  have hM6 : M ^ 6 ≤ N := by
    have h0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have h1 : (M : ℝ) ^ 6 ≤ ((c + 1) * L) ^ 6 := pow_le_pow_left₀ h0 hMup 6
    have h2 : ((c + 1) * L) ^ 6 = (c + 1) ^ 6 * L ^ 6 := by ring
    have h3 : (c + 1) ^ 6 * L ^ 6 ≤ (c + 1) ^ 6 * (1 / (c + 1) ^ 6 * N) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    have h4 : (c + 1) ^ 6 * (1 / (c + 1) ^ 6 * (N : ℝ)) = N := by field_simp
    have : ((M ^ 6 : ℕ) : ℝ) ≤ N := by push_cast; linarith
    exact_mod_cast this
  have htpp := Tpp_le N M hM1 hM6
  rw [← hLdef] at htpp
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNM : (N : ℝ) / M ≤ ε * S N := by
    rw [div_le_iff₀ hMpos]
    have : 2 * S N * L ≤ ε * S N * M := by
      have := mul_le_mul_of_nonneg_left hML (mul_nonneg hε.le hS0)
      nlinarith
    linarith
  calc Tpp N ≤ L * (N / M) := htpp
    _ ≤ L * (ε * S N) := mul_le_mul_of_nonneg_left hNM hLpos.le
    _ = ε * S N * L := by ring

/-- **Goldfeld's count, reduced to one named input.** CONDITIONAL ON `SmallDivBound` only. -/
theorem goldfeld_of_smallDiv (hS : SmallDivBound) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 / 2 - ε) * S N ≤ (((P N).filter
        (fun p => ∃ q, q.Prime ∧ q ∣ N - p ∧ N < q * q)).card : ℝ) := by
  intro ε hε
  exact eventually_atTop.mp (goldfeld_of hS primePowerTail ε hε)

/-- Vacuity for `SmallDivBound`: Tsmall is not identically zero; at N = 4 the term p = 2,
d = 2 gives Tsmall 4 ≥ Λ(2) = log 2 > 0. -/
example : 0 < Tsmall 4 := by
  have hP : (2 : ℕ) ∈ P 4 := by decide
  have hd : (2 : ℕ) ∈ (4 - 2).divisors.filter (fun d => d * d ≤ 4) := by decide
  have h1 : vonMangoldt 2 ≤ ∑ d ∈ (4 - 2).divisors.filter (fun d => d * d ≤ 4), vonMangoldt d :=
    single_le_sum (f := fun d => vonMangoldt d) (fun _ _ => vonMangoldt_nonneg) hd
  have h2 : ∑ d ∈ (4 - 2).divisors.filter (fun d => d * d ≤ 4), vonMangoldt d ≤ Tsmall 4 :=
    single_le_sum (f := fun p => ∑ d ∈ (4 - p).divisors.filter (fun d => d * d ≤ 4), vonMangoldt d)
      (fun _ _ => sum_nonneg (fun _ _ => vonMangoldt_nonneg)) hP
  have h3 : vonMangoldt 2 = Real.log 2 := vonMangoldt_apply_prime Nat.prime_two
  have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Vacuity for the conclusion: at N = 10, p = 3 is good, N - p = 7 with 7² > 10. -/
example : (3 : ℕ) ∈ good 10 := by
  unfold good P
  rw [mem_filter]
  exact ⟨by decide, 7, by norm_num, by norm_num, by norm_num⟩

/-- Vacuity for `Tpp_le`: its hypotheses hold at N = 64, M = 2. -/
example : Tpp 64 ≤ Real.log 64 * ((64 : ℕ) / (2 : ℕ) : ℝ) := by
  have := Tpp_le 64 2 (by norm_num) (by norm_num)
  simpa using this

#print axioms sq_dvd_of_proper_pp
#print axioms pp_part_le
#print axioms sum_inv_sq_tail
#print axioms Tpp_le
#print axioms primePowerTail
#print axioms goldfeld_of_smallDiv

#print axioms log_le_eps
#print axioms primeCounting_le_S_add_one
#print axioms S_mul_log_ge
#print axioms goldfeld_of

#print axioms log_le_split
#print axioms sumLog_le
#print axioms sumLog_ge

end LeanLab.Routes.R0038Goldfeld
