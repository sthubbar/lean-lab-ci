import LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower

/-!
AI wrote this Lean code, burst S117 burst-20261122 round 3. Binary Goldbach is open.
Split of `Decomp243aFeed1122Lower.leaf_linear_sieve_lower`, BJS
https://arxiv.org/abs/2207.09452 p. 43 equation 142, through the Jurkat Richert lower
bound `Decomp1527b.jr_lower`, Iwaniec Kowalski Theorem 11.13. The level satisfies
`z^2 ≤ D ≤ z^4` with `z = N^{1/8}` and `D = √N / (log N)^B` for large `N`, and the error
`(log D)^{-1/3}` is at most `2 (log N)^{-1/3}` since `log D ≥ log N / 4`.
`Decomp1527b` is already imported by `Decomp243a` through `Decomp1527c`, so no cycle.
-/

namespace LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP3

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527b
open LeanLab.AlmostPrimeSums.Decomp243a LeanLab.AlmostPrimeSums.Decomp243aFeed1122Lower

noncomputable section

/-- The prime factors of the sifting primorial are its indexing primes.
BJS p. 37 equation 109. -/
theorem primeFactors_sievePrimorial (N : ℕ) (θ : ℝ) :
    (sievePrimorial N θ).primeFactors = (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
      (p : ℝ) < (N : ℝ) ^ θ ∧ ¬ p ∣ N) := by
  unfold sievePrimorial
  exact Nat.primeFactors_prod (fun p hp => (mem_filter.mp hp).2.1)

/-- BJS p. 43 equations 141 and 142, the sieve setup, formerly a LEAF, now proved. For even `N` the set
`A = {N - p : p < N, p prime, p ∤ N}` with unit weights, sifting primes those of
`P(z) = sievePrimorial N (1/8)`, `X = π(N)` and density `g(d) = 1/φ(d)`, so `g(p) = 1/(p-1)`,
is a `BoundingSieve` whose sifted sum is `S(A, P(z))` and whose remainders are
`r_d = #A_d - X/φ(d)`. The map `p ↦ N - p` is injective on `p < N`. -/
theorem leaf_sieve_instance (N : ℕ) (hN : Even N) :
    ∃ s : BoundingSieve, s.prodPrimes = sievePrimorial N ((1 : ℝ) / 8) ∧
      s.totalMass = (Nat.primeCounting N : ℝ) ∧
      (∀ p ∈ s.prodPrimes.primeFactors, s.nu p = 1 / ((p : ℝ) - 1)) ∧
      s.siftedSum = (SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ) ∧
      ∀ d ∈ s.prodPrimes.divisors, s.rem d =
        (#((range N).filter (fun p => p.Prime ∧ ¬ p ∣ N ∧ d ∣ N - p)) : ℝ)
          - (Nat.primeCounting N : ℝ) / (d.totient : ℝ) := by
  classical
  have hpf := primeFactors_sievePrimorial N ((1 : ℝ) / 8)
  have hsq : Squarefree (sievePrimorial N ((1 : ℝ) / 8)) := by
    unfold sievePrimorial
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (mem_filter.mp hp).2.1 (mem_filter.mp hq).2.1).mpr hpq)
    · intro p hp; exact (mem_filter.mp hp).2.1.squarefree
  let nu : ArithmeticFunction ℝ := ⟨fun d => 1 / (d.totient : ℝ), by simp⟩
  have hnu : ∀ d, nu d = 1 / (d.totient : ℝ) := fun d => rfl
  have hnu_mult : nu.IsMultiplicative := by
    refine ⟨by rw [hnu]; simp, fun {m n} hmn => ?_⟩
    rw [hnu, hnu, hnu, Nat.totient_mul hmn]; push_cast; rw [one_div_mul_one_div]
  have hmemP : ∀ p, p.Prime → p ∣ sievePrimorial N ((1 : ℝ) / 8) → 2 < p := by
    intro p hp hd
    have : p ∈ (sievePrimorial N ((1 : ℝ) / 8)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, hsq.ne_zero⟩
    rw [hpf] at this
    exact (mem_filter.mp this).2.2.1
  set Q := (range N).filter (fun p => p.Prime ∧ ¬ p ∣ N) with hQ
  have hinj : Set.InjOn (fun p => N - p) (Q : Set ℕ) := by
    intro p hp q hq h
    have h1 := mem_range.mp (mem_filter.mp hp).1
    have h2 := mem_range.mp (mem_filter.mp hq).1
    simp only at h; omega
  refine ⟨BoundingSieve.mk (Q.image (fun p => N - p)) (sievePrimorial N ((1 : ℝ) / 8)) hsq
      (fun _ => 1) (fun _ => zero_le_one) (Nat.primeCounting N : ℝ) nu hnu_mult ?_ ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro p hp _
    rw [hnu]; have := Nat.totient_pos.mpr hp.pos; positivity
  · intro p hp hd
    have h2 := hmemP p hp hd
    rw [hnu, Nat.totient_prime hp]
    have : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ p - 1)
    rw [div_lt_one (by linarith)]; linarith
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    show nu p = _
    rw [hnu, Nat.totient_prime hp', Nat.cast_sub hp'.one_le, Nat.cast_one]
  · show (∑ d ∈ Q.image (fun p => N - p),
        if Nat.Coprime (sievePrimorial N ((1 : ℝ) / 8)) d then (1 : ℝ) else 0) = _
    rw [sum_image hinj, sum_boole, SA, idxA, hQ, filter_filter]
    congr 2
    apply filter_congr
    intro p hp
    have hpN := mem_range.mp hp
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hzN : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ N := by
      calc (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ (1 : ℝ) :=
            rpow_le_rpow_of_exponent_le hN1 (by norm_num)
        _ = N := rpow_one _
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun r hr hrz hrN hdvd => ?_⟩
      have hrT : r ∈ (range N).filter (fun p : ℕ => p.Prime ∧ 2 < p ∧
          (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) ∧ ¬ p ∣ N) := by
        refine mem_filter.mpr ⟨mem_range.mpr ?_, hr, ?_, hrz, hrN⟩
        · have : (r : ℝ) < N := lt_of_lt_of_le hrz hzN
          exact_mod_cast this
        · have h2r := hr.two_le
          rcases Nat.lt_or_ge 2 r with h | h
          · exact h
          · exfalso; have : r = 2 := by omega
            subst this; exact hrN (even_iff_two_dvd.mp hN)
      unfold sievePrimorial at h3
      have := Nat.coprime_prod_left_iff.mp h3 r hrT
      exact (Nat.Prime.coprime_iff_not_dvd hr).mp this hdvd
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      unfold sievePrimorial
      apply Nat.coprime_prod_left_iff.mpr
      intro r hr
      obtain ⟨-, hr1, -, hr3, hr4⟩ := mem_filter.mp hr
      exact (Nat.Prime.coprime_iff_not_dvd hr1).mpr (h3 r hr1 hr3 hr4)
  · intro d _
    show (∑ n ∈ Q.image (fun p => N - p), if d ∣ n then (1 : ℝ) else 0) -
        nu d * (Nat.primeCounting N : ℝ) = _
    rw [sum_image hinj, sum_boole, hQ, filter_filter, hnu]
    simp only [and_assoc]
    ring

/-- LEAF: the linear density condition `Ω(κ = 1)` of Iwaniec Kowalski 6.34, equivalently
Halberstam Richert `Ω₂(1)` p. 142, for `g(p) = 1/(p-1)` on the odd sifting primes of BJS
p. 43 equation 142, uniformly in `N`. It follows from Mertens' product theorem together with
`(1 - 1/(p-1))⁻¹ = (1 - 1/p)⁻¹ (1 + 1/(p(p-2)))` and `∏_{p ≥ w} (1 + 1/(p(p-2))) ≤ 1 + O(1/w)`.
Class MEDIUM. -/
theorem leaf_linearDensity_totient :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (w w' : ℝ), 2 ≤ w → w < w' →
      ∏ p ∈ (sievePrimorial N ((1 : ℝ) / 8)).primeFactors.filter
          (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < w'),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤ log w' / log w * (1 + K / log w) := by
  sorry

/-- Error matching for BJS p. 43 equation 142: if `z^2 ≤ D` with `z = N^{1/8}` then
`(log D)^{-1/3} ≤ 2 (log N)^{-1/3}`. -/
theorem logD_rpow_le (N : ℕ) (D : ℝ) (hN : 1 < N)
    (hD : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 ≤ D) :
    log D ^ (-(1 / 3 : ℝ)) ≤ 2 / log N ^ ((1 : ℝ) / 3) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < log (N : ℝ) := log_pos hNr
  have hz2 : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  rw [hz2] at hD
  have hpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have hlog : log N / 8 ≤ log D := by
    have := log_le_log hpos hD
    rw [Real.log_rpow (by linarith)] at this
    linarith
  have h8 : 0 < log (N : ℝ) / 8 := by positivity
  have h1 : (log N / 8) ^ ((1 : ℝ) / 3) ≤ log D ^ ((1 : ℝ) / 3) :=
    rpow_le_rpow h8.le hlog (by norm_num)
  have h2 : (log N / 8) ^ ((1 : ℝ) / 3) = log N ^ ((1 : ℝ) / 3) / 2 := by
    rw [div_rpow hL.le (by norm_num)]
    congr 1
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hLD : 0 < log D := lt_of_lt_of_le h8 hlog
  have hA : 0 < log N ^ ((1 : ℝ) / 3) := by positivity
  rw [Real.rpow_neg hLD.le, ← one_div]
  rw [h2] at h1
  rw [div_le_div_iff₀ (by positivity) hA]
  nlinarith

/-- BJS p. 43 equation 142, `leaf_linear_sieve_lower` with the same statement, from
`Decomp1527b.jr_lower` and the two leaves above. -/
theorem leaf_linear_sieve_lower_of_leaves (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) *
          fsieve (log (sieveLevel N B) / log ((N : ℝ) ^ ((1 : ℝ) / 8)))
        - C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) /
            log N ^ ((1 : ℝ) / 3)
        - sieveRemainder N B ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)) := by
  obtain ⟨K, hK, hden⟩ := leaf_linearDensity_totient
  obtain ⟨C, hC, hjr⟩ := jr_lower K hK
  -- eventually `(log x)^B ≤ x^{1/4}`
  have hev := (isLittleO_log_rpow_rpow_atTop B (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hev
  refine ⟨2 * C, by positivity, max (⌈x0⌉₊) 256, fun N hEven hN => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨hNx, hN256⟩ := hN
  have hNr : (256 : ℝ) ≤ N := by exact_mod_cast hN256
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by have := exp_one_lt_d9; linarith)
  have hLpos : 0 < log (N : ℝ) := by linarith
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hz
  set D := sieveLevel N B with hDdef
  have hz2 : 2 ≤ z := by
    rw [hz, show (2 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 8) by
      rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact rpow_le_rpow (by norm_num) hNr (by norm_num)
  have hzsq : z ^ 2 = (N : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hz4 : z ^ 4 = √(N : ℝ) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]; norm_num
  have hLB1 : 1 ≤ log (N : ℝ) ^ B := Real.one_le_rpow hL1 hB.le
  have hLBpos : 0 < log (N : ℝ) ^ B := by linarith
  have hbound : log (N : ℝ) ^ B ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have := hx0 N (Nat.ceil_le.mp hNx)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLBpos,
      abs_of_pos (by positivity)] at this
    exact this
  have hzD : z ^ 2 ≤ D := by
    rw [hzsq, hDdef, sieveLevel, le_div_iff₀ hLBpos]
    have hsq : √(N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hN0, Real.sqrt_eq_rpow]; norm_num
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have hDz : D ≤ z ^ 4 := by
    rw [hz4, hDdef, sieveLevel]
    exact div_le_self (Real.sqrt_nonneg _) hLB1
  obtain ⟨s, hsP, hsX, hsnu, hsS, hsrem⟩ := leaf_sieve_instance N hEven
  have hpf := primeFactors_sievePrimorial N ((1 : ℝ) / 8)
  have hP : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z := by
    intro p hp
    rw [hsP, hpf] at hp
    exact (mem_filter.mp hp).2.2.2.1
  have hLD : LinearDensity s K := by
    intro w w' hw hww'
    have := hden N w w' hw hww'
    rw [hsP]
    refine le_of_eq_of_le ?_ this
    apply prod_congr rfl
    intro p hp
    have hp' : p ∈ s.prodPrimes.primeFactors := by
      rw [hsP]; exact (mem_filter.mp hp).1
    rw [hsnu p hp']
  have hX : 0 ≤ s.totalMass := by rw [hsX]; positivity
  have hmain := hjr s z D hz2 hzD hDz hP hLD hX
  have hV : (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)) = sieveProduct N ((1 : ℝ) / 8) := by
    rw [sieveProduct, ← hpf, ← hsP]
    apply prod_congr rfl
    intro p hp
    rw [hsnu p hp]
  have hR : ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < D), |s.rem d|
      = sieveRemainder N B := by
    rw [sieveRemainder, ← hsP]
    apply sum_congr rfl
    intro d hd
    rw [hsrem d (mem_filter.mp hd).1]
  rw [hV, hR, hsX, hsS] at hmain
  have herr := logD_rpow_le N D (by omega) (by rw [← hz]; exact hzD)
  have hXV : 0 ≤ (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) :=
    mul_nonneg (by positivity) (sieveProduct_pos _ _).le
  have hL13 : 0 < log (N : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have key : C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) *
      log D ^ (-(1 / 3 : ℝ)) ≤
      2 * C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) /
        log N ^ ((1 : ℝ) / 3) := by
    calc C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) *
          log D ^ (-(1 / 3 : ℝ))
        ≤ C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) *
          (2 / log N ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left herr (mul_nonneg hC.le hXV)
      _ = _ := by ring
  have hexp : (Nat.primeCounting N : ℝ) * (sieveProduct N ((1 : ℝ) / 8) *
      (fsieve (log D / log z) - C * log D ^ (-(1 / 3 : ℝ)))) =
      (Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8) * fsieve (log D / log z)
        - C * ((Nat.primeCounting N : ℝ) * sieveProduct N ((1 : ℝ) / 8)) *
          log D ^ (-(1 / 3 : ℝ)) := by ring
  rw [hexp] at hmain
  linarith

end

#print axioms leaf_linear_sieve_lower_of_leaves
#print axioms leaf_sieve_instance
#print axioms primeFactors_sievePrimorial
#print axioms logD_rpow_le

end LeanLab.AlmostPrimeSums.Decomp243aFeed1122LowerP3
