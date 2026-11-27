/-
Refute1124Lemma11Step: a Lean refutation of leaf306_lemma11_step of Split306Theorem6.lean,
BJS Lemma 11 for n ≥ 2, Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, pages 10 to 13, with display 29 stated, as on page 10, for 1 < u < z only.
The candidate counterexample of notes/burst-20261122/Cai2002-lemma11stepsplit.md is moved to
rational atoms: P = {47, 967, 9973}, g 47 = 3/7, g 967 = 1/4, g 9973 = 2/3, z = D = 10 ^ 12,
n = 3. Every hypothesis is proved here, display 18 from the PROVED leaf306_lemma8. The one
numerical input left is f_3(1) ≤ 2/5, the LEAF cex_f3_le_1124; the true value is about 0.2936.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bLemma11Step

open Finset Real
noncomputable section

namespace LeanLab.Cai2002
namespace Refute1124

/-- The sequence c of the counterexample: c_1 = 1 as stated after BJS display 18, page 6, and
c_n = 0.9607 for n ≥ 2, the constant of BJS Lemma 8, page 7, for which display 18 is the
PROVED leaf306_lemma8. -/
def cexC : ℕ → ℝ := fun n => if n ≤ 1 then 1 else 0.9607

theorem xi_le5 (γ κ ε : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 4) (hκ : κ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) :
    bjsXi306 γ κ ε 1 0.9607 3 ≤ 5 := by
  unfold bjsXi306; nlinarith

theorem exp_le4 (x : ℝ) (hx : x ≤ 1) : exp x ≤ 4 := by
  have he1 : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have := exp_le_exp.mpr hx
  linarith

theorem tau2_cex (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000) :
    0 < bjsTau306 cexC ε 2 ∧ bjsTau306 cexC ε 2 ≤ 15 := by
  have he1 : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  simp only [bjsTau306, cexC]
  norm_num
  refine ⟨Or.inl (Or.inl (Or.inl ?_)), ?_⟩
  · unfold bjsXi306; positivity
  · have key : ∀ γ κ : ℝ, 0 ≤ γ → γ ≤ 4 → κ ≤ 1 → 3 * bjsXi306 γ κ ε 1 (9607/10000) 3 ≤ 15 :=
      fun γ κ a b c => by have := xi_le5 γ κ ε a b c hε0.le hε; norm_num at this; linarith
    simp only [mul_max_of_nonneg _ _ (show (0:ℝ) ≤ 3 by norm_num), max_le_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> apply key <;>
      first | exact exp_le4 _ (by norm_num) | positivity | linarith | norm_num

theorem tau3_cex (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000) :
    bjsTau306 cexC ε 3 ≤ 100 := by
  obtain ⟨ht0, ht⟩ := tau2_cex ε hε0 hε
  have he1 : exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have e3 : bjsTau306 cexC ε 3 = bjsTau306 cexC ε 2 *
      max (bjsXi306 (4 * exp 1 / 3) 0.8349 ε (cexC 2 ^ 1) (cexC 3 ^ 2) (bjsTau306 cexC ε 2))
        (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * (cexC 2 ^ 1) / bjsTau306 cexC ε 2 +
          2 * (2 + ε) * (cexC 3 ^ 2) / bjsTau306 cexC ε 2) := by
    rw [bjsTau306]; simp [show ¬ Even 3 by decide]
  rw [e3]
  set t := bjsTau306 cexC ε 2
  have c2 : cexC 2 = 0.9607 := by simp [cexC]
  have c3 : cexC 3 = 0.9607 := by simp [cexC]
  rw [c2, c3, mul_max_of_nonneg _ _ ht0.le]
  unfold bjsXi306
  apply max_le
  · rw [show t * (0.8349 + (4 * exp 1 / 3 + 0.8349) * ε + 2 * (4 * exp 1 / 3) * 0.9607 ^ 1 / t
        + 2 * 0.9607 ^ 2 / t) = t * 0.8349 + t * (4 * exp 1 / 3 + 0.8349) * ε
        + 2 * (4 * exp 1 / 3) * 0.9607 ^ 1 + 2 * 0.9607 ^ 2 by field_simp]
    have : t * (4 * exp 1 / 3 + 0.8349) * ε ≤ 15 * 5 * 1 := by
      have h1 : 4 * exp 1 / 3 + 0.8349 ≤ 5 := by linarith
      have h2 : 0 ≤ 4 * exp 1 / 3 + 0.8349 := by positivity
      calc t * (4 * exp 1 / 3 + 0.8349) * ε ≤ 15 * 5 * ε := by gcongr
        _ ≤ 15 * 5 * 1 := by nlinarith
    nlinarith
  · rw [show t * (0.9214 + (5 + 4 * ε) * ε + 6 * (1 + ε) * 0.9607 ^ 1 / t
        + 2 * (2 + ε) * 0.9607 ^ 2 / t) = t * (0.9214 + (5 + 4 * ε) * ε)
        + 6 * (1 + ε) * 0.9607 ^ 1 + 2 * (2 + ε) * 0.9607 ^ 2 by field_simp]
    have : (5 + 4 * ε) * ε ≤ 1 := by nlinarith
    nlinarith

/-- The prime values of the multiplicative g of the counterexample, g 47 = 3/7, g 967 = 1/4,
g 9973 = 2/3 and 0 at other primes; g d is their product over the prime factors of d, so the
one parameter display 29 of BJS Lemma 11, page 10, holds with K = 1 at z = 10 ^ 12. -/
def cexGv (p : ℕ) : ℝ := if p = 47 then 3 / 7 else if p = 967 then 1 / 4 else if p = 9973 then 2 / 3 else 0

theorem cexGv_nonneg (p : ℕ) : 0 ≤ cexGv p := by unfold cexGv; split_ifs <;> norm_num

theorem cex_g_prime (q : ℕ) (hq : q.Prime) : ArithmeticFunction.prodPrimeFactors cexGv q = cexGv q := by
  rw [ArithmeticFunction.prodPrimeFactors_apply hq.ne_zero, hq.primeFactors, Finset.prod_singleton]

theorem cex_g_nonneg (d : ℕ) : 0 ≤ ArithmeticFunction.prodPrimeFactors cexGv d := by
  by_cases h : d = 0
  · subst h; simp
  · rw [ArithmeticFunction.prodPrimeFactors_apply h]; exact Finset.prod_nonneg fun p _ => cexGv_nonneg p

theorem p47 : Nat.Prime 47 := by norm_num
theorem p967 : Nat.Prime 967 := by norm_num
theorem p9973 : Nat.Prime 9973 := by norm_num

theorem cex_S : LeanLab.ChenExplicit.primesBelowIn ({47, 967, 9973} : Set ℕ) ((10 : ℝ) ^ 12) =
    {47, 967, 9973} := by
  have hc : ⌈(10 : ℝ) ^ 12⌉₊ = 10 ^ 12 := by
    rw [show (10 : ℝ) ^ 12 = ((10 ^ 12 : ℕ) : ℝ) by norm_num, Nat.ceil_natCast]
  ext p
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range, hc,
    Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem cex_S47 : LeanLab.ChenExplicit.primesBelowIn ({47, 967, 9973} : Set ℕ) ((47 : ℕ) : ℝ) = ∅ := by
  ext p
  simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Finset.mem_range, Nat.ceil_natCast,
    Set.mem_insert_iff, Set.mem_singleton_iff, Finset.notMem_empty, iff_false]
  omega

theorem cex_pf : Nat.primeFactors 453262877 = {47, 967, 9973} := by
  rw [show (453262877 : ℕ) = 47 * (967 * 9973) by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num),
    p47.primeFactors, p967.primeFactors, p9973.primeFactors]
  decide

theorem cex_minFac : Nat.minFac 453262877 = 47 := by norm_num


theorem cex_g47 : ArithmeticFunction.prodPrimeFactors cexGv 47 = 3 / 7 := by
  rw [cex_g_prime 47 p47]; simp [cexGv]
theorem cex_g967 : ArithmeticFunction.prodPrimeFactors cexGv 967 = 1 / 4 := by
  rw [cex_g_prime 967 p967]; simp [cexGv]
theorem cex_g9973 : ArithmeticFunction.prodPrimeFactors cexGv 9973 = 2 / 3 := by
  rw [cex_g_prime 9973 p9973]; simp [cexGv]

theorem cex_V : ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn ({47, 967, 9973} : Set ℕ) ((10 : ℝ) ^ 12),
    (1 - ArithmeticFunction.prodPrimeFactors cexGv p) = 1 / 7 := by
  rw [cex_S]
  simp only [Finset.prod_insert (by decide : (47 : ℕ) ∉ ({967, 9973} : Finset ℕ)),
    Finset.prod_insert (by decide : (967 : ℕ) ∉ ({9973} : Finset ℕ)), Finset.prod_singleton,
    cex_g47, cex_g967, cex_g9973]
  norm_num

theorem cex_T : (1 : ℝ) / 14 ≤ rosserT306 ({47, 967, 9973} : Set ℕ)
    (ArithmeticFunction.prodPrimeFactors cexGv) ((10 : ℝ) ^ 12) ((10 : ℝ) ^ 12) 3 := by
  unfold rosserT306
  rw [cex_S]
  have hN : ∏ p ∈ ({47, 967, 9973} : Finset ℕ), p = 453262877 := by decide
  rw [hN]
  have hmem : (453262877 : ℕ) ∈ (Nat.divisors 453262877).filter (fun d : ℕ =>
      d.primeFactors.card = 3 ∧ (10 : ℝ) ^ 12 ≤ (d : ℝ) * (d.minFac : ℝ) ^ 2 ∧
      ∀ p ∈ d.primeFactors, (d.primeFactors.filter (fun q => p ≤ q)).card < 3 →
        (d.primeFactors.filter (fun q => p ≤ q)).card % 2 = 3 % 2 →
          ((∏ q ∈ d.primeFactors.filter (fun q => p < q), q : ℕ) : ℝ) * (p : ℝ) ^ 3 < (10 : ℝ) ^ 12) := by
    rw [Finset.mem_filter, cex_pf, cex_minFac]
    refine ⟨Nat.mem_divisors_self _ (by norm_num), by decide, by norm_num, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl | rfl)
    · intro h; exact absurd h (by decide)
    · intro _ h; exact absurd h (by decide)
    · intro _ _
      rw [show ({47, 967, 9973} : Finset ℕ).filter (fun q => 9973 < q) = ∅ by decide]
      norm_num
  refine le_trans ?_ (Finset.single_le_sum (f := fun d : ℕ =>
    ArithmeticFunction.prodPrimeFactors cexGv d * ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      ({47, 967, 9973} : Set ℕ) (d.minFac : ℝ), (1 - ArithmeticFunction.prodPrimeFactors cexGv p))
    ?_ hmem)
  · simp only [cex_minFac, cex_S47, Finset.prod_empty, mul_one]
    rw [ArithmeticFunction.prodPrimeFactors_apply (by norm_num), cex_pf]
    simp only [Finset.prod_insert (by decide : (47 : ℕ) ∉ ({967, 9973} : Finset ℕ)),
      Finset.prod_insert (by decide : (967 : ℕ) ∉ ({9973} : Finset ℕ)), Finset.prod_singleton, cexGv]
    norm_num
  · intro d _
    refine mul_nonneg (cex_g_nonneg d) (Finset.prod_nonneg fun p hp => ?_)
    simp only [LeanLab.ChenExplicit.primesBelowIn, Finset.mem_filter, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp.2 with rfl | rfl | rfl
    · rw [cex_g47]; norm_num
    · rw [cex_g967]; norm_num
    · rw [cex_g9973]; norm_num


theorem cex_ratio (K : ℝ) (hK : 1 ≤ K) (a q u : ℝ) (ha : 0 ≤ a) (hu : 1 < u) (huq : u ≤ q)
    (hq : a * log q ≤ log ((10 : ℝ) ^ 12)) : a ≤ K * (log ((10 : ℝ) ^ 12) / log u) := by
  have hlu : 0 < log u := log_pos hu
  have hl : log u ≤ log q := log_le_log (by linarith) huq
  have h1 : a ≤ log ((10 : ℝ) ^ 12) / log u := by
    rw [le_div_iff₀ hlu]; nlinarith
  have h0 : 0 ≤ log ((10 : ℝ) ^ 12) / log u := ha.trans h1
  nlinarith

theorem cex_h29 (K : ℝ) (hK : 1 ≤ K) : ∀ u : ℝ, 1 < u → u < (10 : ℝ) ^ 12 →
    ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn ({47, 967, 9973} : Set ℕ) ((10 : ℝ) ^ 12)).filter
      (fun p : ℕ => u ≤ (p : ℝ)), (1 - ArithmeticFunction.prodPrimeFactors cexGv p)⁻¹ ≤
        K * (log ((10 : ℝ) ^ 12) / log u) := by
  intro u hu1 huz
  have l47 : 7 * log (47 : ℝ) ≤ log ((10 : ℝ) ^ 12) := by
    calc 7 * log (47 : ℝ) = log ((47 : ℝ) ^ 7) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := log_le_log (by norm_num) (by norm_num)
  have l967 : 4 * log (967 : ℝ) ≤ log ((10 : ℝ) ^ 12) := by
    calc 4 * log (967 : ℝ) = log ((967 : ℝ) ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := log_le_log (by norm_num) (by norm_num)
  have l9973 : 3 * log (9973 : ℝ) ≤ log ((10 : ℝ) ^ 12) := by
    calc 3 * log (9973 : ℝ) = log ((9973 : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
      _ ≤ _ := log_le_log (by norm_num) (by norm_num)
  have lz : 1 * log u ≤ log ((10 : ℝ) ^ 12) := by
    rw [one_mul]; exact log_le_log (by linarith) huz.le
  rw [cex_S]
  simp only [Finset.filter_insert, Finset.filter_singleton, Nat.cast_ofNat]
  rcases le_or_gt u 47 with h1 | h1
  · rw [ite_eq_left_of_eq_true _ _ <| eq_true h1, ite_eq_left_of_eq_true _ _ <| eq_true (by linarith), ite_eq_left_of_eq_true _ _ <| eq_true (by linarith)]
    simp only [Finset.prod_insert (by decide : (47 : ℕ) ∉ ({967, 9973} : Finset ℕ)),
      Finset.prod_insert (by decide : (967 : ℕ) ∉ ({9973} : Finset ℕ)), Finset.prod_singleton,
      cex_g47, cex_g967, cex_g9973]
    exact le_trans (le_of_eq (by norm_num)) (cex_ratio K hK 7 47 u (by norm_num) hu1 h1 l47)
  rw [ite_eq_right_of_eq_false _ _ <| eq_false (by linarith)]
  rcases le_or_gt u 967 with h2 | h2
  · rw [ite_eq_left_of_eq_true _ _ <| eq_true h2, ite_eq_left_of_eq_true _ _ <| eq_true (by linarith)]
    simp only [Finset.prod_insert (by decide : (967 : ℕ) ∉ ({9973} : Finset ℕ)), Finset.prod_singleton,
      cex_g967, cex_g9973]
    exact le_trans (le_of_eq (by norm_num)) (cex_ratio K hK 4 967 u (by norm_num) hu1 h2 l967)
  rw [ite_eq_right_of_eq_false _ _ <| eq_false (by linarith)]
  rcases le_or_gt u 9973 with h3 | h3
  · rw [ite_eq_left_of_eq_true _ _ <| eq_true h3]
    simp only [Finset.prod_singleton, cex_g9973]
    exact le_trans (le_of_eq (by norm_num)) (cex_ratio K hK 3 9973 u (by norm_num) hu1 h3 l9973)
  rw [ite_eq_right_of_eq_false _ _ <| eq_false (by linarith)]
  simp only [Finset.prod_empty]
  exact cex_ratio K hK 1 u u (by norm_num) hu1 le_rfl lz

theorem cex_h18 : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) →
    bjsF306 n s ≤ 2 * exp 2 * cexC n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  intro n hn s hs
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have := display18_one306 s (by rcases hs with h | h <;> linarith [h.2])
    simpa using this
  · have hc : cexC n = 0.9607 := by simp [cexC]; omega
    rw [hc]; exact leaf306_lemma8 n h s hs


/-- LEAF: BJS displays 15 to 17, page 6, the value f_3(1) of the functions f_n of the linear sieve,
f_3(1) = integral over t > 3 of f_2(t - 1), about 0.2936 by Simpson's rule, see
notes/burst-20261122/Cai2002-lemma11stepsplit.md, where an independent falsifier found 0.293636.
Only the bound 2/5 is needed. Class MEDIUM: two nested integrals of elementary functions. -/
theorem cex_f3_le_1124 : bjsF306 3 1 ≤ 2 / 5 := by
  sorry

/-- leaf306_lemma11_step of Split306Theorem6.lean, BJS Lemma 11 for n ≥ 2 with the one parameter
display 29, is FALSE given f_3(1) ≤ 2/5: at n = 3, z = D = 10 ^ 12, P = {47, 967, 9973},
ε = 1/2000, K = 1 + 1/4000, c = cexC, the left side is at least V z / 2 with V z = 1/7, and the
right side is at most V z times 2/5 + ε τ_3 with τ_3 ≤ 100. With cex_f3_le_1124 this is a
refutation CONDITIONAL ON that LEAF. -/
theorem leaf306_lemma11_step_refuted_1124 (hf3 : bjsF306 3 1 ≤ 2 / 5) :
    ¬ (∀ (P : Set ℕ) (_ : ∀ p ∈ P, p.Prime) (z : ℝ) (_ : 2 ≤ z)
      (g : ArithmeticFunction ℝ) (_ : g.IsMultiplicative) (_ : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
      (ε : ℝ) (_ : 0 < ε) (K : ℝ) (_ : 1 < K) (_ : K < 1 + ε)
      (_ : ∀ u : ℝ, 1 < u → u < z →
        ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
          (1 - g p)⁻¹ ≤ K * (log z / log u))
      (c : ℕ → ℝ) (_ : ∀ n, 0 < c n)
      (_ : ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) →
        bjsF306 n s ≤ 2 * exp 2 * c n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s)
      (n : ℕ) (_ : 2 ≤ n) (D : ℝ) (_ : 0 < D)
      (_ : (Odd n ∧ 1 ≤ log D / log z) ∨ (Even n ∧ 2 ≤ log D / log z)),
      rosserT306 P g z D n ≤
        (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
          (bjsF306 n (log D / log z) +
            ε * bjsTau306 c ε n * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z))) := by
  intro H
  have hs1 : log ((10 : ℝ) ^ 12) / log ((10 : ℝ) ^ 12) = 1 :=
    div_self (log_pos (by norm_num)).ne'
  have hgp : ∀ p ∈ ({47, 967, 9973} : Set ℕ), 0 ≤ ArithmeticFunction.prodPrimeFactors cexGv p ∧
      ArithmeticFunction.prodPrimeFactors cexGv p < 1 := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · rw [cex_g47]; norm_num
    · rw [cex_g967]; norm_num
    · rw [cex_g9973]; norm_num
  have hP : ∀ p ∈ ({47, 967, 9973} : Set ℕ), p.Prime := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    exacts [p47, p967, p9973]
  have hc : ∀ n, 0 < cexC n := fun n => by unfold cexC; split_ifs <;> norm_num
  have h := H {47, 967, 9973} hP ((10 : ℝ) ^ 12) (by norm_num)
    (ArithmeticFunction.prodPrimeFactors cexGv) (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)
    hgp (1 / 2000) (by norm_num) (1 + 1 / 4000) (by norm_num) (by norm_num)
    (cex_h29 _ (by norm_num)) cexC hc cex_h18 3 (by norm_num) ((10 : ℝ) ^ 12) (by norm_num)
    (Or.inl ⟨by decide, hs1.ge⟩)
  rw [hs1, cex_V, mul_assoc _ (exp 2), lemma11step_exp_hSieve_one] at h
  have hT := cex_T
  have ht := tau3_cex (1 / 2000) (by norm_num) (by norm_num)
  nlinarith

end Refute1124
end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.Refute1124.xi_le5
#print axioms LeanLab.Cai2002.Refute1124.exp_le4
#print axioms LeanLab.Cai2002.Refute1124.tau2_cex
#print axioms LeanLab.Cai2002.Refute1124.tau3_cex
#print axioms LeanLab.Cai2002.Refute1124.cexGv_nonneg
#print axioms LeanLab.Cai2002.Refute1124.cex_g_prime
#print axioms LeanLab.Cai2002.Refute1124.cex_g_nonneg
#print axioms LeanLab.Cai2002.Refute1124.p47
#print axioms LeanLab.Cai2002.Refute1124.p967
#print axioms LeanLab.Cai2002.Refute1124.p9973
#print axioms LeanLab.Cai2002.Refute1124.cex_S
#print axioms LeanLab.Cai2002.Refute1124.cex_S47
#print axioms LeanLab.Cai2002.Refute1124.cex_pf
#print axioms LeanLab.Cai2002.Refute1124.cex_minFac
#print axioms LeanLab.Cai2002.Refute1124.cex_g47
#print axioms LeanLab.Cai2002.Refute1124.cex_g967
#print axioms LeanLab.Cai2002.Refute1124.cex_g9973
#print axioms LeanLab.Cai2002.Refute1124.cex_V
#print axioms LeanLab.Cai2002.Refute1124.cex_T
#print axioms LeanLab.Cai2002.Refute1124.cex_ratio
#print axioms LeanLab.Cai2002.Refute1124.cex_h29
#print axioms LeanLab.Cai2002.Refute1124.cex_h18
#print axioms LeanLab.Cai2002.Refute1124.cex_f3_le_1124
#print axioms LeanLab.Cai2002.Refute1124.leaf306_lemma11_step_refuted_1124
