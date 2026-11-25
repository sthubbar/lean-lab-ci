/-
P0076, Section 4, Proposition 4.1 v, page 16, reference 18 formula 4.1.18.
Proof of the local factor leaf `vdq_local_factor` of VDecayQuadratic1122d.lean by a termwise
bound: each kernel term is at most h of q, the number of pairs a, b of divisors of q with
lcm a b equal to q is at most 3 to the omega of q, and h of q is at most 7/5 to the omega of q
times g of q. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecayQuadratic1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Primes of lcm and gcd: for a, b nonzero with lcm a b equal to q, the primes of a and of b
cover the primes of q and meet in the primes of gcd a b. -/
theorem vdq_pf_union_inter {a b q : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : Nat.lcm a b = q) :
    a.primeFactors ∪ b.primeFactors = q.primeFactors ∧
      a.primeFactors ∩ b.primeFactors = (Nat.gcd a b).primeFactors := by
  have hl0 : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have hg0 : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha0
  refine ⟨?_, (Nat.primeFactors_gcd ha0 hb0).symm⟩
  rw [← Nat.primeFactors_mul ha0 hb0, ← Nat.gcd_mul_lcm a b, Nat.primeFactors_mul hg0 hl0,
    union_eq_right.mpr (Nat.primeFactors_mono (dvd_trans (Nat.gcd_dvd_left a b)
      (Nat.dvd_lcm_left a b)) hl0), hab]

/-- Reference 18 formula 4.1.18, the counting step. For a square free q the pairs a, b of
divisors of q with lcm a b equal to q inject into pairs C inside A inside the primes of q,
via A the primes of a and C the primes of gcd a b, so there are at most the sum over A of
2 to the size of A, which is 3 to the omega of q. -/
theorem vdq_lcm_pairs_card {q : ℕ} (hq : Squarefree q) :
    ((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card ≤
      3 ^ q.primeFactors.card := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have key : ((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card ≤
      (q.primeFactors.powerset.sigma (fun A => A.powerset)).card := by
    apply card_le_card_of_injOn
      (fun x => (⟨x.1.primeFactors, (Nat.gcd x.1 x.2).primeFactors⟩ : Σ _ : Finset ℕ, Finset ℕ))
    · intro x hx
      simp only [coe_filter, mem_product, Nat.mem_divisors, Set.mem_setOf_eq] at hx
      have ha0 : x.1 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hx.1.1.1))
      simp only [coe_sigma, Set.mem_sigma_iff, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
        coe_subset]
      exact ⟨Nat.primeFactors_mono hx.1.1.1 hq0, Nat.primeFactors_mono (Nat.gcd_dvd_left _ _) ha0⟩
    · intro x hx y hy hxy
      simp only [coe_filter, mem_product, Nat.mem_divisors, Set.mem_setOf_eq] at hx hy
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at hxy
      have hx1 : x.1 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hx.1.1.1))
      have hx2 : x.2 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hx.1.2.1))
      have hy1 : y.1 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hy.1.1.1))
      have hy2 : y.2 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hy.1.2.1))
      obtain ⟨hUx, hIx⟩ := vdq_pf_union_inter hx1 hx2 hx.2
      obtain ⟨hUy, hIy⟩ := vdq_pf_union_inter hy1 hy2 hy.2
      have h2 : x.2.primeFactors = y.2.primeFactors := by
        have hC := hxy.2
        rw [← hIx, ← hIy] at hC
        ext p
        have e1 := Finset.ext_iff.mp hUx p
        have e2 := Finset.ext_iff.mp hUy p
        have e3 := Finset.ext_iff.mp hC p
        have e4 := Finset.ext_iff.mp hxy.1 p
        simp only [mem_union, mem_inter] at e1 e2 e3
        tauto
      have sq : ∀ n, n ∣ q → n = ∏ p ∈ n.primeFactors, p := fun n hn =>
        (Nat.prod_primeFactors_of_squarefree (hq.squarefree_of_dvd hn)).symm
      apply Prod.ext
      · rw [sq _ hx.1.1.1, sq _ hy.1.1.1, hxy.1]
      · rw [sq _ hx.1.2.1, sq _ hy.1.2.1, h2]
  refine key.trans (le_of_eq ?_)
  rw [card_sigma]
  have := Finset.sum_pow_mul_eq_add_pow (2 : ℕ) 1 q.primeFactors
  simp only [one_pow, mul_one] at this
  rw [← this]
  apply sum_congr rfl
  intro A _
  rw [card_powerset]

/-- Page 15: h of a square free d is the product of h of p over the primes of d. -/
theorem vdq_h_eq_prod {w d : ℕ} (hd : Squarefree d) :
    envelopingH w d = ∏ p ∈ d.primeFactors, envelopingH w p := by
  unfold envelopingH
  rw [if_pos hd]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [if_pos hpp.squarefree, hpp.primeFactors, prod_singleton]

/-- Page 15 to 16: at a prime p above w at least 5, h of p lies in 0, 2/5 and h of p is at
most 7/5 times g of p. -/
theorem vdq_local_bounds {w p : ℕ} (hw : 5 ≤ w) (hp : p.Prime) (hpw : w < p) :
    0 < envelopingH w p ∧ envelopingH w p ≤ 1 ∧
      envelopingH w p ≤ 7 / 5 * envelopingDensity w p := by
  have hp7 : 7 ≤ p := by
    by_contra h
    have : p = 6 := by omega
    subst this
    exact absurd hp (by decide)
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega; split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega; split_ifs <;> omega
  have hH : envelopingH w p = (envelopingOmega w p : ℝ) / ((p : ℝ) - envelopingOmega w p) := by
    unfold envelopingH
    rw [if_pos hp.squarefree, hp.primeFactors, prod_singleton, Nat.cast_sub (by omega)]
  have hG : envelopingDensity w p = (envelopingOmega w p : ℝ) / p := by
    unfold envelopingDensity
    rw [hp.primeFactors, prod_singleton]
  rw [hH, hG]
  have h1 : (1 : ℝ) ≤ envelopingOmega w p := by exact_mod_cast hom1
  have h2 : (envelopingOmega w p : ℝ) ≤ 2 := by exact_mod_cast hom2
  have h7 : (7 : ℝ) ≤ p := by exact_mod_cast hp7
  have hd : (0 : ℝ) < (p : ℝ) - envelopingOmega w p := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one hd]; linarith
  · rw [div_le_iff₀ hd]
    have hp0 : (0 : ℝ) < p := by linarith
    rw [show 7 / 5 * ((envelopingOmega w p : ℝ) / p) * ((p : ℝ) - envelopingOmega w p)
        = (envelopingOmega w p : ℝ) * (7 / 5 * ((p : ℝ) - envelopingOmega w p) / p) by
          field_simp]
    have : (1 : ℝ) ≤ 7 / 5 * ((p : ℝ) - envelopingOmega w p) / p := by
      rw [le_div_iff₀ hp0]; nlinarith
    nlinarith

/-- Reference 18 formula 4.1.18, termwise: for a, b dividing q with lcm a b equal to q, the
kernel term is at most h of q, since the absolute product is at most the product of one over
h of p over the primes of gcd a b. -/
theorem vdq_term_le {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) {a b : ℕ} (ha : a ∣ q) (hb : b ∣ q)
    (hab : Nat.lcm a b = q) :
    envelopingH w a * envelopingH w b *
        |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)| ≤ envelopingH w q := by
  have hsq : Squarefree q := (enveloping_divisor_support (J := 0) hw hq).1
  have hq0 : q ≠ 0 := hsq.ne_zero
  have ha0 : a ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  have hb0 : b ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hb))
  have hloc : ∀ p ∈ q.primeFactors, 0 < envelopingH w p ∧ envelopingH w p ≤ 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := vdq_local_bounds hw hpp (efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hq))
    exact ⟨this.1, this.2.1⟩
  obtain ⟨hU, hI⟩ := vdq_pf_union_inter ha0 hb0 hab
  have hIsub : (Nat.gcd a b).primeFactors ⊆ q.primeFactors := by
    rw [← hI, ← hU]; exact inter_subset_left.trans subset_union_left
  rw [vdq_h_eq_prod (hsq.squarefree_of_dvd ha), vdq_h_eq_prod (hsq.squarefree_of_dvd hb),
    vdq_h_eq_prod hsq, abs_prod]
  have hbound : ∏ p ∈ (Nat.gcd a b).primeFactors, |1 - 1 / envelopingH w p| ≤
      ∏ p ∈ (Nat.gcd a b).primeFactors, (envelopingH w p)⁻¹ := by
    apply Finset.prod_le_prod₀ (fun p _ => abs_nonneg _)
    intro p hp
    obtain ⟨h0, h1⟩ := hloc p (hIsub hp)
    have : 1 ≤ 1 / envelopingH w p := by rw [le_div_iff₀ h0]; linarith
    rw [abs_of_nonpos (by linarith), one_div]
    have : 0 < (envelopingH w p)⁻¹ := inv_pos.mpr h0
    linarith
  have hnn : 0 ≤ (∏ p ∈ a.primeFactors, envelopingH w p) * ∏ p ∈ b.primeFactors, envelopingH w p :=
    mul_nonneg (prod_nonneg fun p _ => envelopingH_nonneg w p)
      (prod_nonneg fun p _ => envelopingH_nonneg w p)
  refine (mul_le_mul_of_nonneg_left hbound hnn).trans (le_of_eq ?_)
  rw [← prod_union_inter, hU, hI, mul_assoc, ← prod_mul_distrib]
  rw [prod_eq_one (fun p hp => mul_inv_cancel₀ (hloc p (hIsub hp)).1.ne'), mul_one]

/-- The leaf `vdq_local_factor`, Ramare Ruzsa formula 4.1.18, proved outright. -/
theorem vdq_local_factor_proved : type_of% @LeanLab.Teravainen2016.vdq_local_factor := by
  intro w hw z q hq
  have hsq : Squarefree q := (enveloping_divisor_support (J := 0) hw hq).1
  rw [← sum_product' (f := fun a b => if Nat.lcm a b = q then
      envelopingH w a * envelopingH w b *
        |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)| else 0)]
  rw [← sum_filter]
  calc _ ≤ ∑ x ∈ (q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q),
          envelopingH w q := by
        apply sum_le_sum
        intro x hx
        simp only [mem_filter, mem_product, Nat.mem_divisors] at hx
        exact vdq_term_le hw hq hx.1.1.1 hx.1.2.1 hx.2
    _ = (((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card : ℝ) *
          envelopingH w q := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (3 : ℝ) ^ q.primeFactors.card * ((7 / 5 : ℝ) ^ q.primeFactors.card *
          envelopingDensity w q) := by
        have hc : (((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card : ℝ)
            ≤ (3 : ℝ) ^ q.primeFactors.card := by exact_mod_cast vdq_lcm_pairs_card hsq
        refine (mul_le_mul_of_nonneg_right hc (envelopingH_nonneg w q)).trans
          (mul_le_mul_of_nonneg_left ?_ (by positivity))
        · rw [vdq_h_eq_prod hsq, envelopingDensity, ← prod_const, ← prod_mul_distrib]
          apply Finset.prod_le_prod₀ (fun p _ => envelopingH_nonneg w p)
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have := (vdq_local_bounds hw hpp
            (efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hq))).2.2
          unfold envelopingDensity at this
          rwa [hpp.primeFactors, prod_singleton] at this
    _ = (21 / 5 : ℝ) ^ q.primeFactors.card * envelopingDensity w q := by
        rw [← mul_assoc, ← mul_pow]; norm_num

#print axioms vdq_pf_union_inter
#print axioms vdq_lcm_pairs_card
#print axioms vdq_h_eq_prod
#print axioms vdq_local_bounds
#print axioms vdq_term_le
#print axioms vdq_local_factor_proved

end LeanLab.Teravainen2016
