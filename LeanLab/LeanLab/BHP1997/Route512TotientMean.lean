/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, which cites Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, book page 34, display 3.23.
The mean value Σ_{q≤R} (q/φ(q))² ≪ R behind the fact printed under 3.23, PROVED with no
cited input.

Write (q/φ(q))² = Π_{p|q} (p/(p-1))² = Π_{p|q} (1 + h(p)) with h(p) = (2p-1)/(p-1)², so
(q/φ(q))² = Σ_{d|q} h(d) with h(d) = μ(d)² Π_{p|d} h(p), by multiplicativity. Then
Σ_{q≤R} (q/φ(q))² = Σ_{d≤R} h(d) ⌊R/d⌋ ≤ R Σ_d h(d)/d, and Σ_d h(d)/d is at most
Π_{p≤D} (1 + h(p)/p) ≤ exp Σ_p 6 (1/(p-1) - 1/p) ≤ e^6. The weight h(d) is written out
inline, no new definition.
Burst burst-20261124 session S4. AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Section2MS

/-- Vaughan 1981 chapter 3, the elementary identity behind Σ_{q≤R} (q/φ(q))² ≪ R used
under display 3.23 on book page 34: for q ≥ 1, (q/φ(q))² = Σ_{d|q} μ(d)² Π_{p|d} (2p-1)/(p-1)²,
since both sides are multiplicative in q and at a prime power p^k both equal
(p/(p-1))² = 1 + (2p-1)/(p-1)². Class EASY. -/
theorem totient_ratio_sq_divisor_sum512 (q : ℕ) (hq : 1 ≤ q) :
    ((q : ℝ) / (Nat.totient q : ℝ)) ^ 2 =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
  -- the weight as an arithmetic function, and its multiplicativity
  let H : ArithmeticFunction ℝ := ⟨fun d => (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2, by simp⟩
  have hHapp : ∀ d, H d = (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := fun d => rfl
  have hHmul : H.IsMultiplicative := by
    refine ⟨by rw [hHapp]; simp, fun {m n} hmn => ?_⟩
    rw [hHapp, hHapp, hHapp, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
    push_cast
    ring
  have hG : (H * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)).IsMultiplicative :=
    hHmul.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hRHS : ∀ n, ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 =
      (H * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n := by
    intro n
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    exact Finset.sum_congr rfl (fun d _ => (hHapp d).symm)
  rw [hRHS]
  revert hq
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
      Finset.sum_range_succ', Finset.sum_range_succ']
    have hzero : ∀ i ∈ Finset.range j, H (p ^ (i + 1 + 1)) = 0 := by
      intro i _
      rw [hHapp, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp
    rw [Finset.sum_eq_zero hzero, zero_add, zero_add, hHapp, hHapp, pow_zero, pow_one,
      ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
      hp.primeFactors, Nat.primeFactors_one, Finset.prod_singleton, Finset.prod_empty,
      Nat.totient_prime_pow hp (by omega)]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    rw [Nat.cast_mul, Nat.cast_sub hp.one_le]
    push_cast
    field_simp
    ring
  | zero => intro h; omega
  | one => intro _; simp [ArithmeticFunction.coe_mul_zeta_apply]; rw [hHapp]; simp
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [hG.map_mul_of_coprime hab, ← iha (by omega), ← ihb (by omega),
      Nat.totient_mul hab]
    push_cast
    have ha0 : (Nat.totient a : ℝ) ≠ 0 := by
      have := Nat.totient_pos.2 (show 0 < a by omega); positivity
    have hb0 : (Nat.totient b : ℝ) ≠ 0 := by
      have := Nat.totient_pos.2 (show 0 < b by omega); positivity
    field_simp

/-- Vaughan 1981 chapter 3, the convergence behind Σ_{q≤R} (q/φ(q))² ≪ R used under
display 3.23 on book page 34: Σ_d μ(d)² Π_{p|d} (2p-1)/(p-1)² / d converges, uniformly
bounded partial sums. Class MEDIUM: each factor (2p-1)/(p(p-1)²) is at most 6/p², so the
partial sum is at most Π_p (1 + 6/p²), which is finite. -/
theorem totient_ratio_sq_weight_conv512 :
    ∃ B : ℝ, ∀ D : ℕ,
      ∑ d ∈ Finset.Icc 1 D, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        (∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) / d ≤ B := by
  refine ⟨Real.exp 6, fun D => ?_⟩
  set P := (Finset.Icc 1 D).filter Nat.Prime with hP
  set f : ℕ → ℝ := fun p => if 2 ≤ p then (2 * (p : ℝ) - 1) / (((p : ℝ) - 1) ^ 2 * p) else 0
    with hfdef
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [hfdef]
    split_ifs with h
    · have : (2 : ℝ) ≤ p := by exact_mod_cast h
      apply div_nonneg (by linarith) (by positivity)
    · exact le_rfl
  -- step A: each term is the product of f over the prime factors, or zero
  have stepA : ∀ d ∈ Finset.Icc 1 D, (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      (∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) / d =
      if Squarefree d then ∏ p ∈ d.primeFactors, f p else 0 := by
    intro d _
    split_ifs with hsq
    · have hmu : (ArithmeticFunction.moebius d : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        exact_mod_cast this
      have hd : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
        push_cast; rfl
      rw [hmu, one_mul, hd, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      simp only [hfdef, if_pos h2]
      rw [div_div]
    · have hmu : (ArithmeticFunction.moebius d : ℝ) = 0 := by
        have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
        exact_mod_cast this
      rw [hmu]; simp
  rw [Finset.sum_congr rfl stepA, ← Finset.sum_filter]
  -- step B: index by the set of prime factors
  have hinj : Set.InjOn Nat.primeFactors ↑((Finset.Icc 1 D).filter Squarefree) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    rw [← Nat.prod_primeFactors_of_squarefree ha.2, ← Nat.prod_primeFactors_of_squarefree hb.2]
    exact congrArg (fun t => ∏ p ∈ t, p) hab
  rw [← Finset.sum_image (f := fun t => ∏ p ∈ t, f p) hinj]
  -- step C: the sets of prime factors lie in the power set of the primes up to D
  have hsub : ((Finset.Icc 1 D).filter Squarefree).image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨d, hd, rfl⟩ := ht
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [Finset.mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd : p ≤ d := Nat.le_of_mem_primeFactors hp
    rw [hP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpp.one_le, hpd.trans hd.1.2⟩, hpp⟩
  have stepC := Finset.sum_le_sum_of_subset_of_nonneg (f := fun t => ∏ p ∈ t, f p) hsub
    (fun t _ _ => Finset.prod_nonneg (fun p _ => hf0 p))
  -- step D: the Euler product
  have stepD : ∑ t ∈ P.powerset, ∏ p ∈ t, f p ≤ Real.exp (∑ p ∈ P, f p) := by
    rw [← Finset.prod_one_add]
    exact Real.prod_one_add_le_exp_sum P hf0
  -- step E: telescoping, f p ≤ 6 (1/(p-1) - 1/p)
  have htel : ∀ D : ℕ, ∑ n ∈ Finset.Icc 2 (D + 1),
      (6 * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) = 6 * (1 - 1 / ((D : ℝ) + 1)) := by
    intro D
    induction D with
    | zero => simp
    | succ D ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have h1 : (D : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (D : ℝ) + 1 + 1 ≠ 0 := by positivity
      have h3 : (D : ℝ) + 1 + 1 - 1 = D + 1 := by ring
      rw [h3]
      field_simp
      ring
  have hPsub : P ⊆ Finset.Icc 2 (D + 1) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, by omega⟩
  have stepE : ∑ p ∈ P, f p ≤ 6 := by
    have hle : ∀ p ∈ P, f p ≤ 6 * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      intro p hp
      rw [hP, Finset.mem_filter] at hp
      have h2 : 2 ≤ p := hp.2.two_le
      have h2R : (2 : ℝ) ≤ p := by exact_mod_cast h2
      simp only [hfdef, if_pos h2]
      have ha : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hb : (0 : ℝ) < p := by linarith
      have e : 6 * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) = 6 / (((p : ℝ) - 1) * p) := by
        field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos ha hb, mul_pos (mul_pos ha ha) hb]
    have hnn : ∀ n ∈ Finset.Icc 2 (D + 1), n ∉ P →
        0 ≤ 6 * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      intro n hn _
      rw [Finset.mem_Icc] at hn
      have h2R : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
      have : 1 / (n : ℝ) ≤ 1 / ((n : ℝ) - 1) :=
        one_div_le_one_div_of_le (by linarith) (by linarith)
      linarith
    calc ∑ p ∈ P, f p ≤ ∑ p ∈ P, 6 * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) :=
          Finset.sum_le_sum hle
      _ ≤ ∑ n ∈ Finset.Icc 2 (D + 1), 6 * (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub hnn
      _ = 6 * (1 - 1 / ((D : ℝ) + 1)) := htel D
      _ ≤ 6 := by
          have : 0 ≤ 1 / ((D : ℝ) + 1) := by positivity
          linarith
  calc _ ≤ _ := stepC
    _ ≤ _ := stepD
    _ ≤ Real.exp 6 := Real.exp_le_exp.mpr stepE

/-- Vaughan 1981 chapter 3, book page 34, the mean value under display 3.23:
Σ_{q≤R} (q/φ(q))² ≤ C R. PROVED from the two lemmas above: exchange the order of summation and
count the multiples of d up to R. -/
theorem totient_ratio_sq_mean512 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℕ,
      ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) ^ 2 ≤ C * R := by
  obtain ⟨B, hB⟩ := totient_ratio_sq_weight_conv512
  set h : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) ^ 2 *
    ∏ p ∈ d.primeFactors, (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 with hh
  have hh0 : ∀ d, 0 ≤ h d := by
    intro d
    simp only [hh]
    apply mul_nonneg (sq_nonneg _)
    apply Finset.prod_nonneg
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply div_nonneg (by linarith) (sq_nonneg _)
  have hB0 : 0 ≤ B := by
    have := hB 0
    simpa using this
  refine ⟨B, hB0, fun R => ?_⟩
  -- the identity, term by term
  have step1 : ∑ r ∈ Finset.Icc 1 R, ((r : ℝ) / (Nat.totient r : ℝ)) ^ 2 =
      ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors, h d := by
    refine Finset.sum_congr rfl (fun r hr => ?_)
    exact totient_ratio_sq_divisor_sum512 r (Finset.mem_Icc.mp hr).1
  -- exchange the order of summation
  have step2 : ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors, h d =
      ∑ d ∈ Finset.Icc 1 R, ∑ r ∈ (Finset.Icc 1 R).filter (fun r => d ∣ r), h d := by
    rw [Finset.sum_comm' (t' := Finset.Icc 1 R)
      (s' := fun d => (Finset.Icc 1 R).filter (fun r => d ∣ r))]
    intro r d
    simp only [Nat.mem_divisors, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdr, hr0⟩
      have hd : 1 ≤ d := Nat.pos_of_dvd_of_pos hdr (by omega)
      exact ⟨⟨⟨h1, h2⟩, hdr⟩, hd, (Nat.le_of_dvd (by omega) hdr).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdr⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, hdr, by omega⟩
  -- count the multiples
  have step3 : ∀ d ∈ Finset.Icc 1 R,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r => d ∣ r), h d ≤ R * (h d / d) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 R).filter (fun r => d ∣ r)).card = R / d := by
      have e : Finset.Icc 1 R = Finset.Ioc 0 R := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [e]
      exact Nat.Ioc_filter_dvd_card_eq_div R d
    rw [hcard]
    have hle : ((R / d : ℕ) : ℝ) ≤ (R : ℝ) / d := Nat.cast_div_le
    calc ((R / d : ℕ) : ℝ) * h d ≤ ((R : ℝ) / d) * h d :=
          mul_le_mul_of_nonneg_right hle (hh0 d)
      _ = R * (h d / d) := by field_simp
  calc _ = _ := step1
    _ = _ := step2
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (R : ℝ) * (h d / d) := Finset.sum_le_sum step3
    _ = R * ∑ d ∈ Finset.Icc 1 R, h d / d := by rw [Finset.mul_sum]
    _ ≤ R * B := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg R)
        have := hB R
        simpa [hh, mul_div_assoc] using this
    _ = B * R := by ring

end LeanLab.BHP1997.Section2MS

#print axioms LeanLab.BHP1997.Section2MS.totient_ratio_sq_mean512
