/-
P0076, Section 4, Proposition 4.1 v, page 16 after display 4.5.
Split of the HARD leaf `enveloping_v_decay` of EnvelopingFourierSplit.lean into an exact
local evaluation bound, the Ramare and Ruzsa bound for the Selberg quadratic form twisted
at q, and a proved divisor type bound K to the omega of q at most C of epsilon times q to
the epsilon. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.EnvelopingFourierSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: Proposition 4.1 v, page 16, display 4.5 before the character sum is bounded,
class MEDIUM. Expanding the square in display 4.3, the coefficient at a over q is G 1 of z
times the sum over d1, d2 dividing P of z of rho_d1 rho_d2 times the mean over one period
lcm d1 d2 of the indicator of A of lcm d1 d2 against e of a r over q. This mean vanishes
unless q divides lcm d1 d2, as in reference 18 formula 4.1.13; when it does, the Chinese
remainder theorem splits it into g of lcm d1 d2 over q times the local sum at q, and the
local sum at q has norm at most g of q, the trivial bound of reference 18 formula 4.1.17. -/
theorem vdecay_local_eval {J w : ℕ} (hw : 5 ≤ w) (b : ℤ) (M : ℕ) {q a : ℕ}
    (hqP : q ∣ envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10)))
    (ha : a < q) (hcop : Nat.Coprime a q) :
    ‖envelopingVraw w (WW J w) b M q a‖ ≤
      envelopingDensity w q *
        |envelopingG w 1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
          ∑ d1 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
            ∑ d2 ∈ (envelopingPrimeProduct w ((M : ℝ) ^ ((1 : ℝ) / 10))).divisors,
              if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                  envelopingRho w d2 ((M : ℝ) ^ ((1 : ℝ) / 10)) *
                    envelopingDensity w (Nat.lcm d1 d2 / q)
              else 0| := by
  sorry  -- BLOCKED 2026-11-25 FREE-nv-step task3225 vdecay_local_eval: OUT OF REACH
  -- Missing result: trivial bound ‖local character sum at q‖ ≤ envelopingDensity w q (Ramare-Ruzsa 4.1.17).
  -- The proof requires expanding envelopingVraw via efs_F_expand, applying efs_periodic_vanish
  -- for q ∤ lcm(d1,d2), and for q ∣ lcm(d1,d2) using efs_count_lcm to get envelopingDensity w (lcm/q)
  -- times a local character sum at q. The final step needs ‖local sum at q‖ ≤ envelopingDensity w q
  -- which is the cited formula 4.1.17. This local sum bound is not formalized in the repo.
  -- Searched for: local character sum bound, formula 4.1.17 in LeanLab/Teravainen2016/; not found.

/-- LEAF: Proposition 4.1 v, page 16, the bound on w_q sharp in display 4.5, class HARD.
Cited: Ramare and Ruzsa reference 18 formulas 4.1.14 and 4.1.15, with formula 4.1.18 for
the sets K_d of display 4.2. The Selberg quadratic form twisted at q, G 1 of z times the sum
of rho_d1 rho_d2 g of lcm d1 d2 over q over q dividing lcm d1 d2, equals G 1 of z times
w_q sharp times the product of p over p minus omega of p over p dividing q, and is at most
an absolute constant to the number of prime factors of q, uniformly in w and z. Exact
rational checks at w equal 5, 6, 10 and z up to 80 give the constant below 1.3. -/
theorem vdecay_quadratic_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z → ∀ q : ℕ,
      q ∣ envelopingPrimeProduct w z →
        |envelopingG w 1 z *
          ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
            ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
              if q ∣ Nat.lcm d1 d2 then
                envelopingRho w d1 z * envelopingRho w d2 z *
                  envelopingDensity w (Nat.lcm d1 d2 / q)
              else 0| ≤ K ^ q.primeFactors.card := by
  sorry  -- BLOCKED 2026-11-25 FREE-nv-step task3225 vdecay_quadratic_bound: OUT OF REACH
  -- Missing result: uniform K^{ω(q)} bound on the q-twisted Selberg quadratic form (Ramare-Ruzsa 4.1.14/4.1.15).
  -- The required factorization of the double sum over divisors of the squarefree prime product
  -- into a product over prime factors of q, with local bounds at p ∣ q and p ∤ q, is not formalized.
  -- Searched for: quadratic_split, local_twist_le, quadratic_form_factorization in LeanLab/Teravainen2016/;
  -- found no formalization. SelbergIdentity.lean proves the untwisted identity (efs_selberg_identity_proved)
  -- but the twisted version with q-condition and density (lcm/q) requires additional multiplicative lemmas.
  -- This is a full sieve development (CRT factorization of divisor double-sums) not closable in one session.

/-- Page 16, the local density at a square free q is at most 2 to the number of prime
factors of q over q, since omega of p is at most 2. -/
theorem vdecay_density_le (w : ℕ) {q : ℕ} (hq : Squarefree q) :
    envelopingDensity w q ≤ (2 : ℝ) ^ q.primeFactors.card / q := by
  unfold envelopingDensity
  have h1 : ∏ p ∈ q.primeFactors, (envelopingOmega w p : ℝ) / p ≤
      ∏ p ∈ q.primeFactors, (2 : ℝ) / p := by
    apply prod_le_prod₀
    · intro p _; positivity
    · intro p _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      unfold envelopingOmega
      split_ifs <;> norm_num
  refine h1.trans (le_of_eq ?_)
  rw [prod_div_distrib, prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hq]

/-- The divisor type bound: K to the number of prime factors of q is at most a constant
depending on K and epsilon times q to the epsilon. Primes p at least K to the 1 over epsilon
have p to the epsilon at least K, and there are at most K to the 1 over epsilon others. -/
theorem vdecay_omega_pow_le {K : ℝ} (hK : 1 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      K ^ q.primeFactors.card ≤ C * (q : ℝ) ^ ε := by
  set X := K ^ (1 / ε) with hX
  set T := ⌈X⌉₊ with hT
  refine ⟨K ^ T, by positivity, ?_⟩
  intro q hq
  set S := q.primeFactors.filter (fun p : ℕ => (p : ℝ) < X) with hS
  set L := q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) < X) with hL
  have hcard : q.primeFactors.card = S.card + L.card :=
    (card_filter_add_card_filter_not _).symm
  have hSc : S.card ≤ T := by
    calc S.card ≤ (range T).card := by
          apply card_le_card
          intro p hp
          rw [mem_filter] at hp
          rw [mem_range]
          have : (p : ℝ) < T := lt_of_lt_of_le hp.2 (Nat.le_ceil X)
          exact_mod_cast this
      _ = T := card_range T
  have hS' : K ^ S.card ≤ K ^ T := pow_le_pow_right₀ hK hSc
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hKX : X ^ ε = K := by
    rw [hX, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
  have hL' : K ^ L.card ≤ (q : ℝ) ^ ε := by
    calc K ^ L.card = ∏ p ∈ L, K := by rw [prod_const]
      _ ≤ ∏ p ∈ L, (p : ℝ) ^ ε := by
          apply prod_le_prod₀
          · intro p _; linarith
          · intro p hp
            rw [mem_filter] at hp
            rw [← hKX]
            exact Real.rpow_le_rpow hX0 (not_lt.mp hp.2) hε.le
      _ = (∏ p ∈ L, (p : ℝ)) ^ ε := by
          rw [Real.finsetProd_rpow]
          intro p _; positivity
      _ ≤ (q : ℝ) ^ ε := by
          apply Real.rpow_le_rpow (by positivity) _ hε.le
          have hdvd : ∏ p ∈ L, p ∣ q :=
            dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _))
              (Nat.prod_primeFactors_dvd q)
          have := Nat.le_of_dvd (by omega) hdvd
          rw [← Nat.cast_prod]
          exact_mod_cast this
  rw [hcard, pow_add]
  exact mul_le_mul hS' hL' (by positivity) (by positivity)

/-- Assembly: the exact statement of `enveloping_v_decay` from the two leaves above and
the proved density and divisor type bounds. -/
theorem enveloping_v_decay_of_leaves :
    ∃ D : ℝ → ℝ, (∀ ε : ℝ, 0 < ε → 0 < D ε) ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          ∀ ε : ℝ, 0 < ε → ∀ q : ℕ, 1 ≤ q → ∀ a < q, Nat.Coprime a q →
            ‖envelopingV w (WW J w) b M q a‖ ≤ D ε * (q : ℝ) ^ (ε - 1) := by
  obtain ⟨K, hK1, HB⟩ := vdecay_quadratic_bound
  have hK2 : (1 : ℝ) ≤ 2 * K := by linarith
  choose C hC0 hC using fun (ε : ℝ) (hε : 0 < ε) => vdecay_omega_pow_le hK2 hε
  refine ⟨fun ε => if h : 0 < ε then C ε h else 1, ?_, ?_⟩
  · intro ε hε
    simp only [hε, dite_true]
    exact hC0 ε hε
  intro J w hJ hw b hb hbW hamen M hM ε hε q hq a ha hcop
  simp only [hε, dite_true]
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  have hz : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 10) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold envelopingV
  split_ifs with hs
  · obtain ⟨hqP, hsq, -, -, -⟩ := hs
    have hA := vdecay_local_eval (J := J) hw5 b M hqP ha hcop
    have hBq := HB w hw _ hz q hqP
    have hD := vdecay_density_le w hsq
    have hc := hC ε hε q hq
    calc _ ≤ _ := hA
      _ ≤ (2 : ℝ) ^ q.primeFactors.card / q * K ^ q.primeFactors.card :=
          mul_le_mul hD hBq (abs_nonneg _) (by positivity)
      _ = (2 * K) ^ q.primeFactors.card / q := by rw [mul_pow]; ring
      _ ≤ C ε hε * (q : ℝ) ^ ε / q := div_le_div_of_nonneg_right hc hq0.le
      _ = C ε hε * (q : ℝ) ^ (ε - 1) := by
          rw [Real.rpow_sub_one hq0.ne', mul_div_assoc]
  · rw [norm_zero]
    exact mul_nonneg (hC0 ε hε).le (Real.rpow_nonneg hq0.le _)

/-- Twin check: the assembly has exactly the type of the original leaf. -/
theorem enveloping_v_decay_twin : type_of% @LeanLab.Teravainen2016.enveloping_v_decay :=
  enveloping_v_decay_of_leaves

end LeanLab.Teravainen2016
