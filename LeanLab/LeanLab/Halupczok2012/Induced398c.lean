import LeanLab.Halupczok2012.CharExpansion398c

/-!
PPS1984 page 531, second display: if the primitive character `χ₁` mod `q₁` induces `χ` mod `q`,
then `E(z, h, χ₁) - E(z, h, χ) ≪ log q log z`.
Source: Perelli, Pintz, Salerno, Bombieri's theorem in short intervals,
Ann. Sc. Norm. Sup. Pisa 11 (1984) 529 to 539, copy papers/PPS1984.pdf.

Here `χ₁` is Mathlib's `χ.primitiveCharacter` at the conductor level. The two sums differ only
at `n` sharing a factor with `q`, where `χ n = 0` and `‖χ₁ n‖ ≤ 1`; such `n` with `Λ n ≠ 0`
are powers of primes dividing `q`, and they all divide `∏_{p ∣ q} p ^ ⌊log_p N⌋`.
The explicit bound proved is `ω(q) log (z + h) ≤ log₂ q · log (z + h)`.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Resplit398c

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

/-- The number of distinct prime factors of `q ≥ 1` is at most `log₂ q`. -/
lemma card_primeFactors_le_logb {q : ℕ} (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.logb 2 q := by
  have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have h3 : ((2 : ℝ) ^ (q.primeFactors.card : ℝ)) ≤ q := by
    rw [Real.rpow_natCast]; exact_mod_cast h1.trans h2
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hq)]
  exact h3

/-- The von Mangoldt mass of the `n ≤ N` sharing a factor with `q` is at most `ω(q) log N`. -/
lemma sum_vonMangoldt_not_coprime_le {q : ℕ} (hq : 1 ≤ q) (a N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ (Ioc a N).filter (fun n => ¬ n.Coprime q), Λ n ≤
      (q.primeFactors.card : ℝ) * Real.log N := by
  set M : ℕ := ∏ p ∈ q.primeFactors, p ^ Nat.log p N with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsub : ((Ioc a N).filter (fun n => ¬ n.Coprime q)).filter (fun n => Λ n ≠ 0) ⊆
      M.divisors := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn
    obtain ⟨⟨⟨_, hnN⟩, hcop⟩, hΛ⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have hpq : p ∣ q := by
      by_contra hpq
      exact hcop (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq))
    have hpmem : p ∈ q.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hp, hpq, by omega⟩
    have hkle : k ≤ Nat.log p N := Nat.le_log_of_pow_le hp.one_lt hnN
    rw [Nat.mem_divisors]
    refine ⟨?_, hM0⟩
    exact (pow_dvd_pow p hkle).trans (Finset.dvd_prod_of_mem _ hpmem)
  rw [← Finset.sum_filter_ne_zero]
  calc ∑ n ∈ ((Ioc a N).filter (fun n => ¬ n.Coprime q)).filter (fun n => Λ n ≠ 0), Λ n
      ≤ ∑ n ∈ M.divisors, Λ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ = Real.log M := ArithmeticFunction.vonMangoldt_sum
    _ = ∑ p ∈ q.primeFactors, Real.log ((p : ℝ) ^ Nat.log p N) := by
        rw [hM, Nat.cast_prod, Real.log_prod]
        · simp only [Nat.cast_pow]
        · intro p hp
          rw [Nat.cast_pow]
          exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        have hp0 : 0 < ((p : ℝ) ^ Nat.log p N) := by
          have := (Nat.prime_of_mem_primeFactors hp).pos
          positivity
        apply Real.log_le_log hp0
        exact_mod_cast Nat.pow_log_le_self p (by omega)
    _ = (q.primeFactors.card : ℝ) * Real.log N := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `χ` is principal exactly when its primitive character is. -/
lemma primitiveCharacter_eq_one_iff {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  have : NeZero q := ⟨by omega⟩
  constructor
  · intro h
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

/-- PPS1984 page 531, second display, with explicit constant:
`‖E(z, h, χ₁) - E(z, h, χ)‖ ≤ ω(q) log (z + h)`, with `χ₁` the primitive character inducing `χ`. -/
theorem induced_bound_omega {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) {z h : ℝ}
    (hz : 1 ≤ z) (hh : 0 ≤ h) :
    ‖charE z h χ.primitiveCharacter - charE z h χ‖ ≤
      (q.primeFactors.card : ℝ) * Real.log (z + h) := by
  set N := ⌊z + h⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hdiff : charE z h χ.primitiveCharacter - charE z h χ =
      ∑ n ∈ Ioc ⌊z⌋₊ N, (Λ n : ℂ) * (χ.primitiveCharacter n - χ n) := by
    simp only [charE, primitiveCharacter_eq_one_iff hq χ, mul_sub, sum_sub_distrib]
    ring
  have hpt : ∀ n ∈ Ioc ⌊z⌋₊ N, ‖(Λ n : ℂ) * (χ.primitiveCharacter n - χ n)‖ ≤
      if n.Coprime q then 0 else Λ n := by
    intro n _
    split_ifs with hc
    · have hco : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hc
      have := χ.primitiveCharacter_apply_of_isCoprime hco
      simp only [Int.cast_natCast] at this
      rw [this, sub_self, mul_zero, norm_zero]
    · have hχ : χ n = 0 :=
        MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime])
      rw [hχ, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        ArithmeticFunction.vonMangoldt_nonneg]
      calc Λ n * ‖χ.primitiveCharacter n‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
              ArithmeticFunction.vonMangoldt_nonneg
        _ = Λ n := mul_one _
  have hlog : Real.log N ≤ Real.log (z + h) := by
    apply Real.log_le_log (by exact_mod_cast hN)
    exact Nat.floor_le (by linarith)
  calc ‖charE z h χ.primitiveCharacter - charE z h χ‖
      ≤ ∑ n ∈ Ioc ⌊z⌋₊ N, ‖(Λ n : ℂ) * (χ.primitiveCharacter n - χ n)‖ := by
        rw [hdiff]; exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc ⌊z⌋₊ N, (if n.Coprime q then 0 else Λ n) := Finset.sum_le_sum hpt
    _ = ∑ n ∈ (Ioc ⌊z⌋₊ N).filter (fun n => ¬ n.Coprime q), Λ n := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n _
        split_ifs <;> simp_all
    _ ≤ (q.primeFactors.card : ℝ) * Real.log N := sum_vonMangoldt_not_coprime_le hq _ N hN
    _ ≤ (q.primeFactors.card : ℝ) * Real.log (z + h) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)

/-- PPS1984 page 531, second display: `‖E(z, h, χ₁) - E(z, h, χ)‖ ≤ log₂ q · log (z + h)`. -/
theorem induced_bound {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) {z h : ℝ}
    (hz : 1 ≤ z) (hh : 0 ≤ h) :
    ‖charE z h χ.primitiveCharacter - charE z h χ‖ ≤ Real.logb 2 q * Real.log (z + h) := by
  refine (induced_bound_omega hq χ hz hh).trans ?_
  apply mul_le_mul_of_nonneg_right (card_primeFactors_le_logb hq)
  exact Real.log_nonneg (by linarith)

end LeanLab.Halupczok2012.Resplit398c

#print axioms LeanLab.Halupczok2012.Resplit398c.card_primeFactors_le_logb
#print axioms LeanLab.Halupczok2012.Resplit398c.sum_vonMangoldt_not_coprime_le
#print axioms LeanLab.Halupczok2012.Resplit398c.primitiveCharacter_eq_one_iff
#print axioms LeanLab.Halupczok2012.Resplit398c.induced_bound_omega
#print axioms LeanLab.Halupczok2012.Resplit398c.induced_bound
