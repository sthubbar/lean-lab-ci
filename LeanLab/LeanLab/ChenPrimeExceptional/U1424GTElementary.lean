/-
U-1424, PC run 20261021T1403Z-5629, T1 PROVE on P0039, L. Grimmelt and J. Teräväinen,
The Exceptional Set in Goldbach's Problem with two Chen Primes, arXiv 2508.16400.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Theorem 1.1 stays cited, `grimmeltTeravainen` in ChenPrimes.lean.

Elementary pieces of the paper, read from the arXiv HTML, all PROVED unconditional:
* Lemma 3.2, the vector sieve inequality, `vector_sieve_32`;
* eq 1.6 and Section 2.3, the normalised rough indicator `r_P` and its interval version
  `r_[Q,P)`: the split `r_P = r_Q r_[Q,P)`, nonnegativity, vanishing exactly at non-rough `n`;
* the Mertens exponent ratio behind the constant 3/5 of eq 3.7, `mertens_ratio_35`;
* the B₁ size bookkeeping behind U-1395's `S = 1`: the third prime of `n = p₁p₂p₃ ∈ B₁`
  lies above `N^{1/3-δ₁}`, `B1_p3_large`, with `N ≥ 4 (N^{1/3-δ₁})³` from `N^{3δ₁} ≥ 4`;
* the class 4 mod 6 structure of two-Chen representations, `chen_rep_class4`, `chen_rep_three`.
-/
import LeanLab.ExceptionalSet.GrimmeltTeravainen2025Chain
import LeanLab.ExceptionalSet.ChenPrimes

open Finset

namespace LeanLab.ChenPrimeExceptional.U1424

open LeanLab.ExceptionalSet LeanLab.ExceptionalSet.GT2025

/-! ### Lemma 3.2, vector sieve inequality -/

/-- **Lemma 3.2.** If `A⁻ ≤ A ≤ A⁺`, `B⁻ ≤ B ≤ B⁺`, `A ≥ 0` and `B⁺ ≥ 0`, then
`A⁺ B⁻ + (A⁻ - A⁺) B⁺ ≤ A B`. -/
theorem vector_sieve_32 {A Am Ap B Bm Bp : ℝ} (hAm : Am ≤ A) (hAp : A ≤ Ap)
    (hBm : Bm ≤ B) (hBp : B ≤ Bp) (hA : 0 ≤ A) (hB : 0 ≤ Bp) :
    Ap * Bm + (Am - Ap) * Bp ≤ A * B := by
  have h1 : A * Bm ≤ A * B := mul_le_mul_of_nonneg_left hBm hA
  have h2 : (Ap - A) * Bm ≤ (Ap - A) * Bp :=
    mul_le_mul_of_nonneg_left (hBm.trans hBp) (by linarith)
  have h3 : 0 ≤ (A - Am) * Bp := mul_nonneg (by linarith) hB
  nlinarith

/-- Vacuity of Lemma 3.2: the hypotheses hold with every bound strict, and the inequality is
attained, `A = A⁺ = A⁻ = 1`, `B = B⁻ = 2`, `B⁺ = 3`. -/
theorem vector_sieve_32_vacuity :
    (0 : ℝ) ≤ 1 ∧ (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 3 ∧ (1 : ℝ) * 2 + (1 - 1) * 3 = 1 * 2 := by norm_num

/-- The hypothesis `A ≥ 0` of Lemma 3.2 cannot be dropped: `A = A⁻ = A⁺ = -1`, `B⁻ = 0`,
`B = 1`, `B⁺ = 1` gives left side 0 and right side -1. -/
theorem vector_sieve_32_needs_A_nonneg :
    ¬ ((-1 : ℝ) * 0 + (-1 - -1) * 1 ≤ -1 * 1) := by norm_num

/-! ### eq 1.6 and Section 2.3, the normalised rough indicators -/

/-- `r_[Q,P)(n) = ∏_{Q ≤ p < P} (1 - 1/p)⁻¹ 1_{p ∤ n}`, Section 2.3; `rz P = r_[0,P)`. -/
noncomputable def rI (Q P n : ℕ) : ℝ :=
  ∏ p ∈ (Ico Q P).filter Nat.Prime, if p ∣ n then 0 else (p : ℝ) / (p - 1)

theorem rz_eq_rI (P n : ℕ) : rz P n = rI 0 P n := by
  unfold rz rI; rw [Finset.range_eq_Ico]

/-- **Split**: `r_P(n) = r_Q(n) r_[Q,P)(n)` for `Q ≤ P`. -/
theorem rz_split {Q P : ℕ} (h : Q ≤ P) (n : ℕ) : rz P n = rz Q n * rI Q P n := by
  unfold rz rI
  simp only [Finset.prod_filter]
  exact (Finset.prod_range_mul_prod_Ico _ h).symm

theorem rI_nonneg (Q P n : ℕ) : 0 ≤ rI Q P n := by
  unfold rI
  apply Finset.prod_nonneg
  intro p hp
  simp only [mem_filter] at hp
  split_ifs
  · exact le_refl 0
  · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    exact div_nonneg (by linarith) (by linarith)

/-- `r_[Q,P)(n) = 0` exactly when some prime `p ∈ [Q, P)` divides `n`. -/
theorem rI_eq_zero_iff (Q P n : ℕ) :
    rI Q P n = 0 ↔ ∃ p, p.Prime ∧ Q ≤ p ∧ p < P ∧ p ∣ n := by
  unfold rI
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hp, hz⟩
    simp only [mem_filter, mem_Ico] at hp
    refine ⟨p, hp.2, hp.1.1, hp.1.2, ?_⟩
    by_contra hd
    simp only [hd, ite_false] at hz
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have : (p : ℝ) / (p - 1) ≠ 0 := div_ne_zero (by linarith) (by linarith)
    exact this hz
  · rintro ⟨p, hp, hQ, hP, hd⟩
    exact ⟨p, by simp only [mem_filter, mem_Ico]; exact ⟨⟨hQ, hP⟩, hp⟩, by simp [hd]⟩

/-- Vacuity of the indicator: `r_3(1) = 2/(2-1) = 2`, so it is not identically zero, and
`r_3(6) = 0`. -/
theorem rI_vacuity : rI 0 3 1 = 2 ∧ rI 0 3 6 = 0 := by
  constructor
  · unfold rI
    rw [show (Ico 0 3).filter Nat.Prime = {2} by decide]
    simp; norm_num
  · rw [rI_eq_zero_iff]; exact ⟨2, Nat.prime_two, by norm_num, by norm_num, by norm_num⟩

/-! ### The Mertens ratio 3/5 of eq 3.7 -/

/-- `∏_{N^{1/10} ≤ p < N^{1/6}} (1 - 1/p) ~ log N^{1/10} / log N^{1/6} = (1/10)/(1/6) = 3/5`. -/
theorem mertens_ratio_35 : ((1 : ℝ) / 10) / (1 / 6) = 3 / 5 := by norm_num

/-! ### Size bookkeeping for B₁, eq 3.1 -/

/-- For `n = p₁ p₂ p₃` with `p₁ < a`, `p₁ p₂² ≤ N`, `N ≤ 2 n` and `4 a³ ≤ N`, the third prime
satisfies `p₃ > a`. With `a = N^{1/3-δ₁}`: `p₃` lies outside `[N^{1/10}, N^{1/3-δ₁}]`. -/
theorem B1_p3_large {p₁ p₂ p₃ a N : ℝ} (h1 : 0 < p₁) (h2 : 0 < p₂) (h3 : 0 < p₃)
    (hp1 : p₁ < a) (hp2 : p₁ * p₂ ^ 2 ≤ N) (hn : N ≤ 2 * (p₁ * p₂ * p₃)) (ha : 4 * a ^ 3 ≤ N) :
    a < p₃ := by
  by_contra hc
  push Not at hc
  have ha0 : 0 < a := h1.trans hp1
  -- N² ≤ 4 p₁² p₂² p₃² ≤ 4 p₁ N p₃², so N ≤ 4 p₁ p₃² < 4 a · a² ≤ N
  have hN0 : 0 < N := by nlinarith [pow_pos ha0 3]
  have hsq : N ^ 2 ≤ 4 * (p₁ * p₂ * p₃) ^ 2 := by nlinarith
  have hb : 4 * (p₁ * p₂ * p₃) ^ 2 ≤ 4 * p₁ * N * p₃ ^ 2 := by
    have : (p₁ * p₂ * p₃) ^ 2 = p₁ * (p₁ * p₂ ^ 2) * p₃ ^ 2 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hp2 h1.le
    nlinarith [sq_nonneg p₃, mul_le_mul_of_nonneg_right this (sq_nonneg p₃)]
  have hNle : N ≤ 4 * p₁ * p₃ ^ 2 := by nlinarith
  have hp3sq : p₃ ^ 2 ≤ a ^ 2 := by nlinarith
  have : 4 * p₁ * p₃ ^ 2 < 4 * a * a ^ 2 := by
    have := mul_le_mul_of_nonneg_left hp3sq (by linarith : (0:ℝ) ≤ 4 * p₁)
    nlinarith [sq_nonneg a, pow_pos ha0 2]
  nlinarith

/-- `N^{3δ} ≥ 4` gives `4 (N^{1/3-δ})³ ≤ N`, the size condition of `B1_p3_large`. -/
theorem four_cube_le {N δ : ℝ} (hN : 0 < N) (h : 4 ≤ N ^ (3 * δ)) :
    4 * (N ^ ((1 : ℝ) / 3 - δ)) ^ 3 ≤ N := by
  have hc : (N ^ ((1 : ℝ) / 3 - δ)) ^ 3 = N ^ (1 - 3 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; norm_num; ring_nf
  rw [hc]
  have hsplit : N = N ^ (1 - 3 * δ) * N ^ (3 * δ) := by
    rw [← Real.rpow_add hN]; simp
  have hpos : 0 < N ^ (1 - 3 * δ) := Real.rpow_pos_of_pos hN _
  calc 4 * N ^ (1 - 3 * δ) ≤ N ^ (3 * δ) * N ^ (1 - 3 * δ) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = N := by rw [mul_comm]; exact hsplit.symm

/-- Vacuity of `B1_p3_large`: `p₁ = 1`, `p₂ = 2`, `p₃ = 3`, `a = 3/2`, `N = 12` meet every
hypothesis, `4 a³ = 13.5 > 12` fails, so take `a = 1.4`: `4 · 2.744 = 10.976 ≤ 12`. -/
theorem B1_p3_large_vacuity :
    (0 : ℝ) < 1 ∧ (1 : ℝ) < 1.4 ∧ (1 : ℝ) * 2 ^ 2 ≤ 12 ∧ (12 : ℝ) ≤ 2 * (1 * 2 * 3) ∧
      4 * (1.4 : ℝ) ^ 3 ≤ 12 ∧ (1.4 : ℝ) < 3 := by norm_num

/-! ### Two-Chen representations of m ≡ 4 mod 6 -/

private lemma even_prime {p : ℕ} (hp : p.Prime) (h : p % 2 = 0) : p = 2 := by
  have := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h); omega

private lemma three_prime {p : ℕ} (hp : p.Prime) (h : p % 3 = 0) : p = 3 := by
  have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h); omega

/-- **Class 4 mod 6.** A sum `m = p + q ≡ 4 mod 6` of two primes is `2 + 2`, or uses a 3, or
has both primes `≡ 5 mod 6`. -/
theorem prime_rep_class4 {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hm : m % 6 = 4)
    (hpq : p + q = m) :
    (p = 2 ∧ q = 2) ∨ (p = 3 ∧ q % 6 = 1) ∨ (q = 3 ∧ p % 6 = 1) ∨
      (p % 6 = 5 ∧ q % 6 = 5) := by
  have p2 := hp.two_le
  have q2 := hq.two_le
  by_cases hp2 : p % 2 = 0
  · have := even_prime hp hp2
    subst this
    have : q = 2 := even_prime hq (by omega)
    exact Or.inl ⟨rfl, this⟩
  by_cases hq2 : q % 2 = 0
  · have := even_prime hq hq2; omega
  by_cases hp3 : p % 3 = 0
  · have := three_prime hp hp3; subst this; omega
  by_cases hq3 : q % 3 = 0
  · have := three_prime hq hq3; subst this; omega
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := by omega
  right; right; right
  rcases hp6 with h | h <;> rcases hq6 with h' | h' <;> omega

/-- With Chen primes, a representation of `m ≡ 4 mod 6` through the summand 3 forces
`m = 3 r + 1` with `r` prime, by `chen_one_mod_six`. -/
theorem chen_rep_three {q m : ℕ} (hq : IsChenPrime q) (hm : m % 6 = 4) (h : 3 + q = m) :
    ∃ r, r.Prime ∧ m = 3 * r + 1 := by
  have hq1 : q % 6 = 1 := by omega
  obtain ⟨r, hr, hqr⟩ := chen_one_mod_six hq hq1
  exact ⟨r, hr, by omega⟩

/-- **Two-Chen representations of `m ≡ 4 mod 6`, `m > 4`:** both primes are `≡ 5 mod 6`, or
`m = 3 r + 1` with `r` prime. -/
theorem chen_rep_class4 {p q m : ℕ} (hp : IsChenPrime p) (hq : IsChenPrime q)
    (hm : m % 6 = 4) (h4 : 4 < m) (hpq : p + q = m) :
    (p % 6 = 5 ∧ q % 6 = 5) ∨ ∃ r, r.Prime ∧ m = 3 * r + 1 := by
  rcases prime_rep_class4 hp.1 hq.1 hm hpq with h | h | h | h
  · omega
  · exact Or.inr (chen_rep_three hq hm (by omega))
  · exact Or.inr (chen_rep_three hp hm (by omega))
  · exact Or.inl h

/-- Vacuity: `10 = 5 + 5`, both Chen and `≡ 5 mod 6`; `16 = 3 + 13`, `13 + 2 = 15 = 3 · 5`,
so `13` is a Chen prime `≡ 1 mod 6` and `16 = 3 · 5 + 1`. -/
theorem chen_rep_vacuity : IsChenPrime 5 ∧ IsChenPrime 13 ∧ IsChenPrime 3 := by
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors,
      ArithmeticFunction.cardFactors_apply_prime (by norm_num)]; norm_num
  · rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors, show (13 + 2 : ℕ) = 3 * 5 by norm_num,
      ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime (by norm_num),
      ArithmeticFunction.cardFactors_apply_prime (by norm_num)]
  · rw [LeanLab.AlmostPrimes.bigOmega_eq_cardFactors,
      ArithmeticFunction.cardFactors_apply_prime (by norm_num)]; norm_num

end LeanLab.ChenPrimeExceptional.U1424

#print axioms LeanLab.ChenPrimeExceptional.U1424.vector_sieve_32
#print axioms LeanLab.ChenPrimeExceptional.U1424.vector_sieve_32_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1424.vector_sieve_32_needs_A_nonneg
#print axioms LeanLab.ChenPrimeExceptional.U1424.rz_eq_rI
#print axioms LeanLab.ChenPrimeExceptional.U1424.rz_split
#print axioms LeanLab.ChenPrimeExceptional.U1424.rI_nonneg
#print axioms LeanLab.ChenPrimeExceptional.U1424.rI_eq_zero_iff
#print axioms LeanLab.ChenPrimeExceptional.U1424.rI_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1424.mertens_ratio_35
#print axioms LeanLab.ChenPrimeExceptional.U1424.B1_p3_large
#print axioms LeanLab.ChenPrimeExceptional.U1424.four_cube_le
#print axioms LeanLab.ChenPrimeExceptional.U1424.B1_p3_large_vacuity
#print axioms LeanLab.ChenPrimeExceptional.U1424.prime_rep_class4
#print axioms LeanLab.ChenPrimeExceptional.U1424.chen_rep_three
#print axioms LeanLab.ChenPrimeExceptional.U1424.chen_rep_class4
#print axioms LeanLab.ChenPrimeExceptional.U1424.chen_rep_vacuity
