/-
P0069 Baker, Harman and Pintz 1997, page 3 condition i display 1.7, pages 24 to 27
and pages 41 and 42. A necessary condition for the OPEN leaf upper_mean_value_supply
of Decomp312b. Any witness of that leaf, pushed through the proved Perron transfer
of Decomp312a, bounds the number of primes in the short interval I by the count of I
times u1 / log x, up to Y L^(-A) for every A. So the leaf is at least as strong as
the upper bound half of the main theorem of the paper, and no elementary witness
can meet it. Nothing here proves or refutes the leaf. The leaf stays OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b

namespace LeanLab.BHP1997.Upper312Prove
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132

/-- P0069, page 3, condition i, display 1.7, read at q = 1, the trivial character
and t = x, with display 1.3 of page 2, `rho(k) <= a1(k)` on I. A family with the
character distribution at density u that dominates the prime indicator on I for
large x bounds the number of primes in I. PROVED. AI wrote the Lean code.
Goldbach is open.
Plain math: `Σ_{k ∈ I} ρ(k) ≤ |I| u / log x + C x^(11/20+ε) L^(-A)` for x ≥ C. -/
theorem prime_count_le_of_distribution {ε u : ℝ} {a : ℝ → ℕ → ℝ}
    (hd : CharacterDistribution ε u a)
    (hlo : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ k ∈ leftInterval ε x, primeWeight k ≤ a x k) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ k ∈ leftInterval ε x, primeWeight k ≤
        ((leftInterval ε x).card : ℝ) * (u / Real.log x) +
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := hd A hA
  obtain ⟨X, hX⟩ := hlo
  refine ⟨max (max C0 (Real.exp 1)) X, fun x hx => ?_⟩
  have hxC : C0 ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hxX : X ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hlogA : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hlog1 hA.le
  have hh := hC0 x hxC 1 le_rfl (by simpa using hlogA) 1 x le_rfl
  have hfilter : (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ x) = leftInterval ε x := by
    refine Finset.filter_true_of_mem fun k hk => ?_
    have hk2 : k ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hk).2
    exact (Nat.cast_le.mpr hk2).trans (Nat.floor_le hx0.le)
  rw [hfilter] at hh
  have hδ : Thm2.delta (1 : DirichletCharacter ℂ 1) = 1 := by simp [Thm2.delta]
  have he : (∑ k ∈ leftInterval ε x,
      ((a x k : ℂ) * (1 : DirichletCharacter ℂ 1) (k : ZMod 1) -
        Thm2.delta (1 : DirichletCharacter ℂ 1) * u / Real.log x)) =
      ((∑ k ∈ leftInterval ε x, (a x k - u / Real.log x) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : (k : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [h1, map_one, hδ]
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hh
  have hup := (le_abs_self _).trans hh
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hup
  have hdom : ∑ k ∈ leftInterval ε x, primeWeight k ≤ ∑ k ∈ leftInterval ε x, a x k :=
    Finset.sum_le_sum fun k hk => hX x hxX k hk
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (by linarith) _
  have hCmono : C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
      max (max C0 (Real.exp 1)) X * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_max_left _ _)) hY) hL
  linarith

/-- P0069, pages 24 to 27 with pages 41 and 42. The conclusion of the OPEN leaf
upper_mean_value_supply, copied verbatim as the hypothesis, gives through the proved
Perron transfer a threshold below which every eps has a density constant u1 below
1.0001 that bounds the number of primes in I. This is the upper bound half of the
main theorem of the paper with constant 1.0001, so the leaf cannot have an
elementary witness. PROVED, with the leaf conclusion as hypothesis, so it is a
necessary condition and not a proof of the leaf. AI wrote the Lean code.
Goldbach is open.
Plain math: `π(x) - π(x - 2Y) ≤ |I| u1 / log x + C Y L^(-A)`, `Y = x^(11/20+ε)`. -/
theorem upper_mean_value_supply_prime_count_necessary
    (hsupply : ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ u1 : ℝ, 1 ≤ u1 ∧ u1 < 1.0001 ∧
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          ∑ k ∈ leftInterval ε x, primeWeight k ≤
            ((leftInterval ε x).card : ℝ) * (u1 / Real.log x) +
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨B0, ηs, _, hηs, hs⟩ := hsupply
  obtain ⟨ηp, hηp, hp⟩ := perron_transfer B0
  refine ⟨min ηs ηp, lt_min hηs hηp, fun ε hε hεη => ?_⟩
  obtain ⟨u, c, b, hu, hu1, _, hb, hm, hd, happ, hlo⟩ :=
    hs ε hε (lt_of_lt_of_le hεη (min_le_left _ _))
  have hr := hp ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) b hb hm
  exact ⟨u, hu, hu1, prime_count_le_of_distribution
    (distribution_of_approximation happ (distribution_of_reference hε.le hr hd)) hlo⟩

end LeanLab.BHP1997.Upper312Prove

#print axioms LeanLab.BHP1997.Upper312Prove.prime_count_le_of_distribution
#print axioms LeanLab.BHP1997.Upper312Prove.upper_mean_value_supply_prime_count_necessary
