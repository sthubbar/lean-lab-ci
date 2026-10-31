import LeanLab.Routes.U1431SelbergBV
import LeanLab.PNTSieve.BrunTitchmarshAP
import LeanLab.PNTSieve.MertensProduct
import LeanLab.PNTSieve.MertensUpper

/-
# U-1436, I-0104, track T2: the lower bound for the Selberg sum of the Goldbach sieve

Unit U-1436, PC run 20261021T1403Z-5629. AI-written Lean code, Claude. Checked only by the Lean
kernel. KNOWN mathematics: Selberg's upper bound sieve, the Bombieri-Davenport form of the
Goldbach upper bound. Binary Goldbach is OPEN; an upper bound on r(N) is not progress on it.

Plain-math twins, statement by statement:
* `selbergS_ge_aux`: S(N, z, y), the Selberg sum of U-1431's `gbSieve` with g(p) = 1/(p - 2), is at
  least the Selberg sum of the same sifting set and level with density 1/n, g(p) = 1/(p - 1).
* `selbergS_ge`: for N ≥ 1, z, 1 ≤ y ≤ z², S(N, z, y) ≥ (φ(2N)/(2N)) · (log y)/2.
  Proof: S ≥ Σ_{m ≤ √y, (m, 2N) = 1} 1/m ≥ (φ(2N)/(2N)) log(⌊√y⌋ + 1).
* `totient_two_mul_even`: for even N, φ(2N) = 2 φ(N), so φ(2N)/(2N) = φ(N)/N.
* `rG_le_main_bv`: for every A > 0 there are B > 0 and K with, for all even N ≥ 2, z and
  1 < y ≤ min(z², √N/(log N)^B),
  r(N) ≤ 2 (N/φ(N)) li(N - 1)/log y + √((N + li(N - 1)) M₉(N, z) K N/(log N)^A) + z + 1.
  With y about √N/(log N)^B, log y about (log N)/2, the first term is about
  4 (N/φ(N)) N/(log N)² = 8 ∏_{p ∣ N, p > 2} p/(p - 1) · N/(log N)².
* `M9_le`: M₉(N, z) ≤ exp(126) (log z)⁹ for z ≥ 2, from Σ_{p ≤ z} 1/p ≤ log log z + 12.
-/

namespace LeanLab.Routes.U1436

open Finset LeanLab.PNTPort.BVMax LeanLab.Routes.U1431
open LeanLab.PNTSieve.Sieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open scoped ArithmeticFunction.omega ArithmeticFunction.zeta

/-! ## A. An auxiliary sieve with the completely multiplicative density 1/n -/

/-- Same sifting product and level as `gbSieve`, density `1/n`. Only its Selberg sum is used. -/
noncomputable def auxSieve (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := goldbachSeq N
  prodPrimes := Pprod N z
  prodPrimes_squarefree :=
    LeanLab.PNTSieve.Sieve.prodDistinctPrimes_squarefree _ (fun p hp => (mem_Pset.1 hp).2.1)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := liD ((N - 1 : ℕ) : ℝ)
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := y
  one_le_level := hy

lemma aux_nu_apply (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) {n : ℕ} (hn : n ≠ 0) :
    (auxSieve N z y hy).nu n = 1 / (n : ℝ) := by
  simp [auxSieve, ArithmeticFunction.pdiv_apply, hn]

lemma gb_nu_apply (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) (n : ℕ) :
    (gbSieve N z y hy).nu n = nuG N n := rfl

/-- Termwise comparison of the two Selberg sums. PROVED. -/
theorem selbergS_ge_aux (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    selbergBoundingSum (auxSieve N z y hy) ≤ selbergBoundingSum (gbSieve N z y hy) := by
  unfold selbergBoundingSum
  apply sum_le_sum
  intro l hl
  have hlP : l ∣ Pprod N z := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors hl)
  show (if l ^ 2 ≤ y then _ else 0) ≤ (if l ^ 2 ≤ y then _ else 0)
  split_ifs with h
  · rw [LeanLab.PNTSieve.SelbergSieve.selbergTerms_apply,
      LeanLab.PNTSieve.SelbergSieve.selbergTerms_apply]
    have hc : Nat.Coprime l N := Nat.Coprime.coprime_dvd_left hlP (Pprod_coprime N z)
    have hν : (auxSieve N z y hy).nu l ≤ (gbSieve N z y hy).nu l := by
      rw [aux_nu_apply N z y hy hl0, gb_nu_apply, nuG_apply, if_pos hc, one_div]
      have hφ : (0 : ℝ) < l.totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0)
      exact inv_anti₀ hφ (by exact_mod_cast Nat.totient_le l)
    have hprime : ∀ p ∈ l.primeFactors,
        0 ≤ 1 / (1 - (auxSieve N z y hy).nu p) ∧
        1 / (1 - (auxSieve N z y hy).nu p) ≤ 1 / (1 - (gbSieve N z y hy).nu p) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpP : p ∈ Pset N z := prime_dvd_Pprod hpp ((Nat.dvd_of_mem_primeFactors hp).trans hlP)
      obtain ⟨_, _, h3, hpN⟩ := mem_Pset.1 hpP
      have hcp : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hpp).2 hpN
      rw [aux_nu_apply N z y hy hpp.ne_zero, gb_nu_apply, nuG_apply, if_pos hcp,
        Nat.totient_prime hpp]
      have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hcast]
      have ha : 0 < 1 - 1 / (p : ℝ) := by
        have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
        linarith
      have hb : 0 < 1 - ((p : ℝ) - 1)⁻¹ := by
        have : ((p : ℝ) - 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        linarith
      refine ⟨(one_div_pos.2 ha).le, one_div_le_one_div_of_le hb ?_⟩
      have : 1 / (p : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (by linarith) (by linarith)
      linarith
    have hnu0 : 0 ≤ (auxSieve N z y hy).nu l := by
      rw [aux_nu_apply N z y hy hl0]; positivity
    apply mul_le_mul hν (Finset.prod_le_prod₀ (fun p hp => (hprime p hp).1) (fun p hp => (hprime p hp).2))
      (prod_nonneg (fun p hp => (hprime p hp).1)) (hnu0.trans hν)
  · exact le_rfl

/-! ## B. The lower bound for S -/

/-- **Lower bound for the Selberg sum.** For `N ≥ 1` and `1 ≤ y ≤ z²`,
`S(N, z, y) ≥ (φ(2N)/(2N)) · (log y)/2`. PROVED. -/
theorem selbergS_ge (N z : ℕ) (hN : 1 ≤ N) (y : ℝ) (hy : 1 ≤ y) (hyz : y ≤ (z : ℝ) ^ 2) :
    ((2 * N).totient : ℝ) / (2 * N : ℕ) * (Real.log y / 2) ≤
      selbergBoundingSum (gbSieve N z y hy) := by
  classical
  set s := auxSieve N z y hy with hs
  have hy0 : 0 < y := by linarith
  have hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id := rfl
  have hsqz : Real.sqrt y ≤ z := by
    rw [Real.sqrt_le_left (by positivity)]; exact hyz
  have hbs := LeanLab.PNTSieve.Sieve.boundingSum_ge_sum_filter s
    (fun m => 1 ≤ m ∧ Nat.Coprime m (2 * N) ∧ m ≤ ⌊Real.sqrt y⌋₊)
    (by
      intro m hm p hp hpm
      have hm1 : 1 ≤ m := hm.1
      have hpm' : p ≤ m := Nat.le_of_dvd hm1 hpm
      have hmz : (m : ℝ) ≤ z := by
        have : (m : ℝ) ≤ ⌊Real.sqrt y⌋₊ := by exact_mod_cast hm.2.2
        exact this.trans ((Nat.floor_le (Real.sqrt_nonneg y)).trans hsqz)
      have hpz : p ≤ z := by
        have : (p : ℝ) ≤ z := (by exact_mod_cast hpm' : (p : ℝ) ≤ m).trans hmz
        exact_mod_cast this
      have hpc : Nat.Coprime p (2 * N) := Nat.Coprime.coprime_dvd_left hpm hm.2.1
      have hp2 : ¬ p ∣ 2 * N := (Nat.Prime.coprime_iff_not_dvd hp).mp hpc
      have hp3 : 3 ≤ p := by
        rcases Nat.lt_or_ge p 3 with h | h
        · exfalso
          have : p = 2 := by have := hp.two_le; omega
          exact hp2 (this ▸ dvd_mul_right 2 N)
        · exact h
      have hpN : ¬ p ∣ N := fun h => hp2 (h.trans (dvd_mul_left N 2))
      show p ∣ Pprod N z
      exact dvd_prod_of_mem _ (mem_Pset.2 ⟨hpz, hp, hp3, hpN⟩))
    (by rw [hnu]; exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id)
    (by
      intro n; rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      simp)
    (by
      intro p hpp _
      rw [hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [ite_eq_right, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero)
  have hfilt : ∑ m ∈ (Icc 1 ⌊Real.sqrt s.level⌋₊).filter
        (fun m => 1 ≤ m ∧ Nat.Coprime m (2 * N) ∧ m ≤ ⌊Real.sqrt y⌋₊), s.nu m =
      ∑ m ∈ (Icc 1 ⌊Real.sqrt y⌋₊).filter (fun m => Nat.Coprime m (2 * N)), (1 : ℝ) / m := by
    have hl : s.level = y := rfl
    rw [hl]
    apply sum_congr
    · ext m; simp only [mem_filter, mem_Icc]; constructor
      · rintro ⟨⟨h1, h2⟩, _, h3, _⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h1, h3, h2⟩
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm
      rw [hs, aux_nu_apply N z y hy (show m ≠ 0 by omega)]
  have hharm := LeanLab.PNTPort.BVMax.coprime_harm_ge (2 * N) ⌊Real.sqrt y⌋₊ (by omega)
  have hlogsq : Real.log y / 2 ≤ Real.log ((⌊Real.sqrt y⌋₊ : ℝ) + 1) := by
    rw [← Real.log_sqrt hy0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hy0) (Nat.lt_floor_add_one _).le
  have h1 : ((2 * N).totient : ℝ) / (2 * N : ℕ) * (Real.log y / 2) ≤
      ((2 * N).totient : ℝ) / (2 * N : ℕ) * Real.log ((⌊Real.sqrt y⌋₊ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlogsq (by positivity)
  have h2 : ∑ m ∈ (Icc 1 ⌊Real.sqrt y⌋₊).filter (fun m => Nat.Coprime m (2 * N)), (1 : ℝ) / m ≤
      selbergBoundingSum s := by
    rw [← hfilt]
    have := hbs
    rw [ge_iff_le] at this
    convert this using 1
    exact sum_congr (by ext m; simp only [mem_filter]) (fun _ _ => rfl)
  have h3 := selbergS_ge_aux N z y hy
  have h4 : ((2 * N).totient : ℝ) / (2 * N : ℕ) * Real.log ((⌊Real.sqrt y⌋₊ : ℝ) + 1) ≤
      ∑ m ∈ (Icc 1 ⌊Real.sqrt y⌋₊).filter (fun m => Nat.Coprime m (2 * N)), (1 : ℝ) / m := by
    exact_mod_cast hharm
  linarith

/-- For even `N`, `φ(2N) = 2 φ(N)`. PROVED. -/
theorem totient_two_mul_even {N : ℕ} (hN : 2 ∣ N) : (2 * N).totient = 2 * N.totient :=
  Nat.totient_mul_of_prime_of_dvd Nat.prime_two hN

/-! ## C. The main term: r(N) ≤ 2 (N/φ(N)) li(N - 1)/log y + BV error + z + 1 -/

/-- For even `N` and `1 < y ≤ z²`: `li(N - 1)/S ≤ 2 (N/φ(N)) li(N - 1)/log y`. PROVED. -/
theorem li_div_S_le {N : ℕ} (hN : 2 ≤ N) (hev : 2 ∣ N) (z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (hy1 : 1 < y) (hyz : y ≤ (z : ℝ) ^ 2) :
    liD ((N - 1 : ℕ) : ℝ) / selbergBoundingSum (gbSieve N z y hy) ≤
      2 * ((N : ℝ) / N.totient) * liD ((N - 1 : ℕ) : ℝ) / Real.log y := by
  have hS := selbergS_ge N z (by omega) y hy hyz
  rw [totient_two_mul_even hev] at hS
  have hφ : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hly : 0 < Real.log y := Real.log_pos hy1
  have he : ((2 * N.totient : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) * (Real.log y / 2) =
      (N.totient : ℝ) / N * (Real.log y / 2) := by
    push_cast; field_simp
  rw [he] at hS
  have hpos : 0 < (N.totient : ℝ) / N * (Real.log y / 2) := by positivity
  calc liD ((N - 1 : ℕ) : ℝ) / selbergBoundingSum (gbSieve N z y hy)
      ≤ liD ((N - 1 : ℕ) : ℝ) / ((N.totient : ℝ) / N * (Real.log y / 2)) :=
        div_le_div_of_nonneg_left (liD_nonneg _) hpos hS
    _ = 2 * ((N : ℝ) / N.totient) * liD ((N - 1 : ℕ) : ℝ) / Real.log y := by
        field_simp

/-- **Bombieri-Davenport shape, unconditional.** For every `A > 0` there are `B > 0` and `K` with,
for all even `N ≥ 2`, all `z` and all `1 < y ≤ min(z², √N/(log N)^B)`,
`r(N) ≤ 2 (N/φ(N)) li(N - 1)/log y + √((N + li(N - 1)) M₉(N, z) K N/(log N)^A) + z + 1`.
PROVED. -/
theorem rG_le_main_bv (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    2 ∣ N → ∀ z : ℕ, ∀ y : ℝ, 1 < y → y ≤ (z : ℝ) ^ 2 → y ≤ Real.sqrt N / Real.log N ^ B →
    (rG N : ℝ) ≤ 2 * ((N : ℝ) / N.totient) * liD ((N - 1 : ℕ) : ℝ) / Real.log y +
      Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * M9 N z * (K * N / Real.log N ^ A)) +
      (z + 1) := by
  obtain ⟨B, hB, K, hK⟩ := rG_le_selberg_bv A hA
  refine ⟨B, hB, K, fun N hN hev z y hy1 hyz hyB => ?_⟩
  have h := hK N hN z y hy1.le hyB
  have h2 := li_div_S_le hN hev z y hy1.le hy1 hyz
  linarith

/-! ## D. The Mertens type bound M₉(N, z) ≤ exp(126) (log z)⁹ -/

/-- `d ↦ 9^ω(d)/φ(d)`, multiplicative. -/
noncomputable def f9 : ArithmeticFunction ℝ :=
  ⟨fun d => (9 : ℝ) ^ ω d / (d.totient : ℝ), by simp⟩

lemma f9_apply (d : ℕ) : f9 d = (9 : ℝ) ^ ω d / (d.totient : ℝ) := rfl

lemma f9_mult : f9.IsMultiplicative := by
  refine ⟨by simp [f9_apply], fun {m n} hmn => ?_⟩
  simp only [f9_apply]
  rw [ArithmeticFunction.cardDistinctFactors_mul hmn, Nat.totient_mul hmn, pow_add, Nat.cast_mul,
    mul_div_mul_comm]

/-- Plain-math twin: `M₉(N, z) = ∏_{3 ≤ p ≤ z, p ∤ N} (1 + 9/(p - 1))`. PROVED. -/
theorem M9_eq_prod (N z : ℕ) :
    M9 N z = ∏ p ∈ Pset N z, (1 + 9 / ((p : ℝ) - 1)) := by
  have hsq : Squarefree (Pprod N z) :=
    LeanLab.PNTSieve.Sieve.prodDistinctPrimes_squarefree _ (fun p hp => (mem_Pset.1 hp).2.1)
  have h := f9_mult.prodPrimeFactors_one_add_of_squarefree hsq
  have hpf : (Pprod N z).primeFactors = Pset N z :=
    Nat.primeFactors_prod (fun p hp => (mem_Pset.1 hp).2.1)
  rw [hpf] at h
  unfold M9
  rw [← show ∑ d ∈ (Pprod N z).divisors, f9 d =
      ∑ d ∈ (Pprod N z).divisors, (9 : ℝ) ^ ω d / (d.totient : ℝ) from rfl, ← h]
  refine prod_congr rfl (fun p hp => ?_)
  have hpp := (mem_Pset.1 hp).2.1
  have h3 := (mem_Pset.1 hp).2.2.1
  rw [f9_apply, ArithmeticFunction.cardDistinctFactors_apply_prime hpp, Nat.totient_prime hpp,
    pow_one, Nat.cast_sub (by omega)]
  simp

/-- **Mertens type bound.** For `z ≥ 2`, `M₉(N, z) ≤ exp(126) (log z)⁹`. PROVED. -/
theorem M9_le (N z : ℕ) (hz : 2 ≤ z) :
    M9 N z ≤ Real.exp 126 * Real.log z ^ 9 := by
  rw [M9_eq_prod]
  have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hLz : 0 < Real.log z := Real.log_pos (by linarith)
  have hp3 : ∀ p ∈ Pset N z, (3 : ℝ) ≤ p := fun p hp => by exact_mod_cast (mem_Pset.1 hp).2.2.1
  -- each factor is at most exp(9/(p - 1))
  have h1 : ∏ p ∈ Pset N z, (1 + 9 / ((p : ℝ) - 1)) ≤
      Real.exp (9 * ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1)) := by
    rw [mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro p hp; have := hp3 p hp; have : 0 < (p : ℝ) - 1 := by linarith
      positivity
    · intro p hp
      have := Real.add_one_le_exp (9 * (1 / ((p : ℝ) - 1)))
      have e : 9 * (1 / ((p : ℝ) - 1)) = 9 / ((p : ℝ) - 1) := by ring
      rw [e] at this ⊢; linarith
  -- Σ 1/(p - 1) ≤ Σ 1/p + Σ 1/(p - 1)²
  have h2 : ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1) ≤
      ∑ p ∈ Pset N z, (1 : ℝ) / p + ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    exact LeanLab.PNTSieve.Mertens.inv_pred_le p (by have := (mem_Pset.1 hp).2.2.1; omega)
  have hsub : Pset N z ⊆ (Icc 1 z).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpz, hpp, h3, _⟩ := mem_Pset.1 hp
    simp only [mem_filter, mem_Icc]
    exact ⟨⟨by omega, hpz⟩, hpp⟩
  have h3 : ∑ p ∈ Pset N z, (1 : ℝ) / p ≤ Real.log (Real.log z) + 12 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (LeanLab.PNTSieve.Mertens.sum_inv_primes_le z hz)
  have h4 : ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1) ^ 2 ≤ 2 := by
    have hinj : Set.InjOn (fun p : ℕ => (p - 1 : ℕ)) (Pset N z : Set ℕ) := by
      intro a ha b hb hab
      have := (mem_Pset.1 ha).2.2.1
      have := (mem_Pset.1 hb).2.2.1
      simp only at hab; omega
    have himg : (Pset N z).image (fun p : ℕ => (p - 1 : ℕ)) ⊆ Icc 1 z := by
      intro n hn
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hn
      obtain ⟨hpz, _, h3, _⟩ := mem_Pset.1 hp
      simp only [mem_Icc]; omega
    calc ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1) ^ 2
        = ∑ n ∈ (Pset N z).image (fun p : ℕ => (p - 1 : ℕ)), (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl (fun p hp => ?_)
          have := (mem_Pset.1 hp).2.2.1
          rw [Nat.cast_sub (by omega)]; simp
      _ ≤ ∑ n ∈ Icc 1 z, (1 : ℝ) / (n : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ ≤ 2 := LeanLab.PNTSieve.Mertens.sum_inv_sq_le_two z
  have h5 : Real.exp (9 * ∑ p ∈ Pset N z, 1 / ((p : ℝ) - 1)) ≤
      Real.exp (126 + 9 * Real.log (Real.log z)) :=
    Real.exp_le_exp.2 (by linarith)
  have h6 : Real.exp (126 + 9 * Real.log (Real.log z)) = Real.exp 126 * Real.log z ^ 9 := by
    rw [Real.exp_add]
    congr 1
    rw [show (9 : ℝ) * Real.log (Real.log z) = ((9 : ℕ) : ℝ) * Real.log (Real.log z) by norm_num,
      ← Real.log_pow, Real.exp_log (by positivity)]
  linarith

/-- The `rG_le_main_bv` bound with `M₉` replaced by `exp(126) (log z)⁹`, for `z ≥ 2`. PROVED. -/
theorem rG_le_main_bv_mertens (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ, 2 ≤ N → 2 ∣ N → ∀ z : ℕ, 2 ≤ z → ∀ y : ℝ, 1 < y → y ≤ (z : ℝ) ^ 2 →
    y ≤ Real.sqrt N / Real.log N ^ B →
    (rG N : ℝ) ≤ 2 * ((N : ℝ) / N.totient) * liD ((N - 1 : ℕ) : ℝ) / Real.log y +
      Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * (Real.exp 126 * Real.log z ^ 9) *
        (K * N / Real.log N ^ A)) + (z + 1) := by
  obtain ⟨B, hB, K, hK⟩ := rG_le_main_bv A hA
  refine ⟨B, hB, max K 0, le_max_right _ _, fun N hN hev z hz y hy1 hyz hyB => ?_⟩
  have h := hK N hN hev z y hy1 hyz hyB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N ^ A := Real.rpow_pos_of_pos (Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))) A
  have hNX : 0 ≤ (N : ℝ) + liD ((N - 1 : ℕ) : ℝ) := add_nonneg hN0.le (liD_nonneg _)
  have hM0 : 0 ≤ M9 N z := by
    unfold M9; exact sum_nonneg (fun d _ => by positivity)
  have hsq : Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * M9 N z * (K * N / Real.log N ^ A)) ≤
      Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * (Real.exp 126 * Real.log z ^ 9) *
        (max K 0 * N / Real.log N ^ A)) := by
    apply Real.sqrt_le_sqrt
    have hK' : K * N / Real.log N ^ A ≤ max K 0 * N / Real.log N ^ A := by
      apply div_le_div_of_nonneg_right _ hlogN.le
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hN0.le
    have hK0 : 0 ≤ max K 0 * N / Real.log N ^ A := by
      apply div_nonneg (mul_nonneg (le_max_right _ _) hN0.le) hlogN.le
    rcases le_or_gt 0 (K * N / Real.log N ^ A) with hk | hk
    · apply mul_le_mul (mul_le_mul_of_nonneg_left (M9_le N z hz) hNX) hK' hk
      exact mul_nonneg hNX (by positivity)
    · have : ((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * M9 N z * (K * N / Real.log N ^ A) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hNX hM0) hk.le
      exact this.trans (mul_nonneg (mul_nonneg hNX (by positivity)) hK0)
  linarith

/-! ## E. Vacuity instances -/

/-- `selbergS_ge` at `N = 10`, `z = 3`, `y = 9`: the hypotheses hold and the bound is
`(φ(20)/20)(log 9)/2 = (2/5) log 3 > 0`, so the statement is live. -/
theorem vacuity_S : (1 : ℕ) ≤ 10 ∧ (1 : ℝ) ≤ 9 ∧ (9 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 2 ∧
    (0 : ℝ) < ((2 * 10).totient : ℝ) / (2 * 10 : ℕ) * (Real.log 9 / 2) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  have : 0 < (2 * 10).totient := Nat.totient_pos.mpr (by norm_num)
  have h9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  positivity

/-- `Pset 10 7 = {3, 7}`: `M₉(10, 7) = (1 + 9/2)(1 + 9/6) = 13.75`, so `M9_le` is a statement about a
nontrivial product. -/
theorem vacuity_M9 : Pset 10 7 = {3, 7} := by decide

/-- `li_div_S_le` hypotheses are satisfiable: `N = 10` even, `z = 3`, `y = 9`, `1 < 9 ≤ 3²`. -/
theorem vacuity_main : 2 ≤ 10 ∧ 2 ∣ 10 ∧ (1 : ℝ) < 9 ∧ (9 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 2 := by
  norm_num

end LeanLab.Routes.U1436

#print axioms LeanLab.Routes.U1436.selbergS_ge_aux
#print axioms LeanLab.Routes.U1436.selbergS_ge
#print axioms LeanLab.Routes.U1436.totient_two_mul_even
#print axioms LeanLab.Routes.U1436.li_div_S_le
#print axioms LeanLab.Routes.U1436.rG_le_main_bv
#print axioms LeanLab.Routes.U1436.M9_eq_prod
#print axioms LeanLab.Routes.U1436.M9_le
#print axioms LeanLab.Routes.U1436.rG_le_main_bv_mertens
#print axioms LeanLab.Routes.U1436.vacuity_S
#print axioms LeanLab.Routes.U1436.vacuity_M9
#print axioms LeanLab.Routes.U1436.vacuity_main
