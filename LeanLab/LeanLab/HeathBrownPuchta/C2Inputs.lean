import LeanLab.HeathBrownPuchta.C2Discharge

/-!
# Heath-Brown and Puchta 2002: the grouping and Möbius inputs of `C2_le_conditional`

Lab proof, unit U-1284, PC run 20261020T2004Z-7678. AI wrote the Lean code. P0012, arXiv
math/0201299 v2, Section 5, (35) to (41).

PROVED unconditional:
* `dvd_iff_eps_dvd`: `d ∣ 2^n - 1 ↔ ε(d) ∣ n`, every `d` and `n`.
* `h_eq_sum_k`: `h(n) = Σ_{d ∣ n} k(d)` for `n ≠ 0`.
* `sum_kappaTrue_divisors`: `Σ_{e ∣ m} κ(e) = h(2^m - 1)` for `m > 0`.
* `kappaTrue_eq_kappa`: `κ(e) = Σ_{d ∣ e} μ(e/d) h(2^d - 1)` for every `e ≥ 1`, by Möbius inversion.
* `grouping`: `C₂ = Σ_e κ(e+1)/(e+1)` as `tsum`s, with no summability hypothesis.
CONDITIONAL: `C2_le_of_LLW`, `C₂ ≤ 2.2141`, and `c2Inputs_of_LLW`, ON the Liu, Liu and Wang
input `llw` alone. Binary Goldbach is OPEN.
-/

namespace LeanLab.HeathBrownPuchta.C2Inputs

open Finset LeanLab.HeathBrownPuchta.Lemma8Const

/-! ## Grouping by the order of 2 -/

/-- `d ∣ 2^n - 1` exactly when `ε(d) ∣ n`. -/
theorem dvd_iff_eps_dvd (d n : ℕ) : d ∣ 2 ^ n - 1 ↔ eps d ∣ n := by
  rw [eps, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- The fiber `{d : ε(d) = e}` as a finset. -/
noncomputable def S (e : ℕ) : Finset ℕ := (2 ^ e - 1).divisors.filter (fun d => eps d = e)

/-- The summand of (35). -/
noncomputable def f (d : ℕ) : ℝ := (k d : ℝ) / eps d

theorem f_nonneg (d : ℕ) : 0 ≤ f d :=
  div_nonneg (by exact_mod_cast k_nonneg d) (Nat.cast_nonneg _)

theorem indicator_zero (e d : ℕ) (hd : d ∉ S e) : {d | eps d = e}.indicator f d = 0 := by
  by_cases he : eps d = e
  · rcases Nat.eq_zero_or_pos e with h0 | hpos
    · simp [Set.indicator, he, f, h0]
    · exfalso; apply hd
      simp only [S, Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨(dvd_iff_eps_dvd d e).2 (he ▸ dvd_rfl), ?_⟩, he⟩
      have := Nat.one_lt_two_pow hpos.ne'
      omega
  · simp [Set.indicator, he]

theorem fiber_summable (e : ℕ) : Summable fun c : {d // eps d = e} => f c := by
  have : Summable ({d | eps d = e}.indicator f) :=
    summable_of_ne_finset_zero (s := S e) fun d hd => indicator_zero e d hd
  exact (summable_subtype_iff_indicator (s := {d | eps d = e})).2 this

theorem fiber_tsum (e : ℕ) : ∑' c : {d // eps d = e}, f c = kappaTrue e / e := by
  have h1 : ∑' c : {d // eps d = e}, f c = ∑' d, {d | eps d = e}.indicator f d :=
    tsum_subtype {d | eps d = e} f
  rw [h1, tsum_eq_sum (s := S e) fun d hd => indicator_zero e d hd, kappaTrue, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have he : eps d = e := (Finset.mem_filter.1 hd).2
  simp [Set.indicator, he, f]

/-- Grouping of (35) by `ε(d)`: `C₂ = Σ_e κ(e+1)/(e+1)`, no summability assumed. -/
theorem grouping : C2 = ∑' e : ℕ, kappaTrue (e + 1) / ((e : ℝ) + 1) := by
  let σ := Equiv.sigmaFiberEquiv eps
  have hC : C2 = ∑' p : (Σ e, {d // eps d = e}), f (σ p) := by
    rw [C2, Equiv.tsum_eq σ f]; rfl
  have hG : ∀ p : (Σ e, {d // eps d = e}), f (σ p) = f p.2.1 := fun p => rfl
  have hiff := summable_sigma_of_nonneg (f := fun p : (Σ e, {d // eps d = e}) => f (σ p))
    (fun p => f_nonneg _)
  let F : ℕ → ℝ := fun e => kappaTrue e / e
  have hF0 : F 0 = 0 := by simp [F]
  have hinner : ∀ e, ∑' c : {d // eps d = e}, f (σ ⟨e, c⟩) = F e := fun e => fiber_tsum e
  have hsum : C2 = ∑' e, F e := by
    rw [hC]
    by_cases hs : Summable fun p : (Σ e, {d // eps d = e}) => f (σ p)
    · rw [hs.tsum_sigma' (fun e => fiber_summable e)]
      exact tsum_congr hinner
    · have hn : ¬ Summable F := by
        intro hF; apply hs; rw [hiff]
        exact ⟨fun e => fiber_summable e, by simpa [hinner] using hF⟩
      rw [tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable hn]
  have hshift : ∑' e, F e = ∑' e : ℕ, kappaTrue (e + 1) / ((e : ℝ) + 1) := by
    have hcongr : (fun e : ℕ => F (e + 1)) = fun e : ℕ => kappaTrue (e + 1) / ((e : ℝ) + 1) := by
      funext e; simp [F]
    by_cases hs : Summable fun e : ℕ => F (e + 1)
    · rw [tsum_eq_zero_add' hs, hF0, zero_add, hcongr]
    · have hn : ¬ Summable F := fun hF => hs ((summable_nat_add_iff 1).2 hF)
      rw [tsum_eq_zero_of_not_summable hn, ← hcongr, tsum_eq_zero_of_not_summable hs]
  rw [hsum, hshift]

/-! ## The divisor sum of `k` -/

theorem sqf_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) : Squarefree (∏ p ∈ t, p) := by
  have := Finset.squarefree_prod_of_pairwise_isCoprime (s := t) (f := id)
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (ht p hp) (ht q hq)).mpr hpq))
    (fun p hp => (ht p hp).prime.squarefree)
  simpa using this

/-- `k(p)` at a prime, `0` at `2`. -/
noncomputable def g (p : ℕ) : ℚ := if p = 2 then 0 else 1 / ((p : ℚ) - 2)

theorem k_eq_prod_g (d : ℕ) (hd : Squarefree d) : k d = ∏ p ∈ d.primeFactors, g p := by
  unfold k
  by_cases ho : Odd d
  · rw [if_pos ⟨ho, hd⟩]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
    simp [g, hp2]
  · rw [if_neg (fun h => ho h.1)]
    have h2 : 2 ∈ d.primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, ?_, hd.ne_zero⟩
      exact even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 ho)
    exact (Finset.prod_eq_zero h2 (by simp [g])).symm

/-- `h(n) = Σ_{d ∣ n} k(d)`, Section 5. -/
theorem h_eq_sum_k (n : ℕ) (hn : n ≠ 0) : h n = ∑ d ∈ n.divisors, k d := by
  classical
  have step1 : h n = ∏ p ∈ n.primeFactors, (1 + g p) := by
    unfold h
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hp2 : p = 2
    · simp [hp2, g]
    · have h3 : 3 ≤ p := by have := hpp.two_le; omega
      have h3' : (3 : ℚ) ≤ p := by exact_mod_cast h3
      have hne : (p : ℚ) - 2 ≠ 0 := by linarith
      rw [if_pos hp2]
      simp only [g, hp2, ite_false]
      field_simp
      ring
  rw [step1, Finset.prod_one_add]
  rw [← Finset.sum_filter_of_ne (s := n.divisors) (f := k) (p := fun d : ℕ => Squarefree d) (fun d _ hk => by
    by_contra hs; exact hk (by simp [k, hs]))]
  symm
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun t => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    simp only [Finset.mem_powerset]
    exact Nat.primeFactors_mono hd.1.1 hn
  · intro t ht
    simp only [Finset.mem_powerset] at ht
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn⟩, sqf_prod_primes t hpr⟩
    exact (Finset.prod_dvd_prod_of_subset _ _ _ ht).trans (Nat.prod_primeFactors_dvd n)
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.1 hd).2
  · intro t ht
    simp only [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  · intro d hd
    exact k_eq_prod_g d (Finset.mem_filter.1 hd).2

/-! ## Möbius inversion -/

theorem pow_sub_one_ne_zero (m : ℕ) (hm : 0 < m) : 2 ^ m - 1 ≠ 0 := by
  have := Nat.one_lt_two_pow hm.ne'
  omega

/-- `Σ_{e ∣ m} κ(e) = h(2^m - 1)`. -/
theorem sum_kappaTrue_divisors (m : ℕ) (hm : 0 < m) :
    ∑ e ∈ m.divisors, kappaTrue e = (h (2 ^ m - 1) : ℝ) := by
  rw [h_eq_sum_k _ (pow_sub_one_ne_zero m hm), Rat.cast_sum]
  have hmaps : ∀ d ∈ (2 ^ m - 1).divisors, eps d ∈ m.divisors := fun d hd => by
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨(dvd_iff_eps_dvd d m).1 hd.1, hm.ne'⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun d => (k d : ℝ))
  rw [← hfib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Nat.mem_divisors] at he
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he.1 hm
  unfold kappaTrue
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, _⟩, hde⟩
    exact ⟨⟨(dvd_iff_eps_dvd d m).2 (hde ▸ he.1), pow_sub_one_ne_zero m hm⟩, hde⟩
  · rintro ⟨⟨_, _⟩, hde⟩
    exact ⟨⟨(dvd_iff_eps_dvd d e).2 (hde ▸ dvd_rfl), pow_sub_one_ne_zero e hepos⟩, hde⟩

/-- The paper's `κ(e) = Σ_{d ∣ e} μ(e/d) h(2^d - 1)` for every `e ≥ 1`. -/
theorem kappaTrue_eq_kappa (e : ℕ) (he : 1 ≤ e) : kappaTrue e = (kappa e : ℝ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := kappaTrue) (g := fun n => (h (2 ^ n - 1) : ℝ))).1 sum_kappaTrue_divisors e he
  rw [← key, Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) *
    (h (2 ^ b - 1) : ℝ))]
  simp only [kappa, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

/-! ## `C₂ ≤ 2.2141` from Liu, Liu and Wang alone -/

/-- `C₂ ≤ 2.2141`. CONDITIONAL ON `llw`, the Liu, Liu and Wang input
`Σ_{e < n} κ(e+1) ≤ 2.744 log n` for `n ≥ 24`. -/
theorem C2_le_of_LLW
    (llw : ∀ n, 24 ≤ n → ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2744 / 1000 * Real.log n) :
    C2 ≤ 22141 / 10000 :=
  C2_le_conditional grouping (fun e h1 _ => kappaTrue_eq_kappa e h1) llw

/-- The `C2Inputs` structure of `C2Discharge.lean` from `llw` alone. CONDITIONAL ON `llw`. -/
theorem c2Inputs_of_LLW
    (llw : ∀ n, 24 ≤ n → ∑ e ∈ range n, kappaTrue (e + 1) ≤ 2744 / 1000 * Real.log n) :
    C2Discharge.C2Inputs :=
  ⟨grouping, fun e h1 _ => kappaTrue_eq_kappa e h1, llw⟩

end LeanLab.HeathBrownPuchta.C2Inputs
