/-
P0076, Section 4, Proposition 4.1 v, page 16, display 4.5.
Split of the HARD leaf `vdecay_quadratic_bound` of VDecay1122b.lean into the exact Selberg
diagonalization of the twisted quadratic form at q, a proved truncated mass bound by G_1,
and a local factor bound at the primes of q. The assembly is proved.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecay1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: Proposition 4.1 v, page 16, display 4.5 with w_q sharp from reference 18 formulas
4.1.14 and 4.1.15, class HARD. The Selberg diagonalization with y variables y_m equal to
h of m over G 1 of z for m dividing P of z with m at most z, so that rho_d is mu of d over
g of d times the sum of y_m over the multiples m of d. Writing g of lcm d1 d2 as g d1 g d2
over g of gcd d1 d2 and one over g of a square free k as the sum over e dividing k of one
over h of e, the twisted form at q collapses to the diagonal sum over n coprime to q of
h of n times a kernel over pairs a, b of divisors of q with lcm a b equal to q. Checked with
exact rationals for w equal 5, 6, 10, integer z up to 31 and every q dividing P of z. -/
theorem vdq_selberg_diagonal {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    envelopingG w 1 z *
        ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              envelopingRho w d1 z * envelopingRho w d2 z *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0) =
      (-1 : ℝ) ^ q.primeFactors.card / (envelopingDensity w q * envelopingG w 1 z) *
        ∑ n ∈ (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q),
          envelopingH w n *
            ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
              (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                envelopingH w a * envelopingH w b *
                  ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
              else 0) := by
  sorry

/-- LEAF: Proposition 4.1 v, page 16, the local factor of w_q sharp at the primes of q, as
in reference 18 formula 4.1.18, class MEDIUM. The kernel of the diagonalization in absolute
value, summed over pairs a, b of divisors of q with lcm a b equal to q, is multiplicative in
q with local factor 2 h of p plus h of p times the absolute value of h of p minus 1 at each
prime p of q. Since h of p is at most 2 over 5 and g of p is h of p times 1 minus g of p,
this local factor over g of p is at most 3 over 1 minus g of p, at most 21 over 5. -/

/- Helper: primes of lcm and gcd. For a, b nonzero with lcm a b equal to q, the primes of
a and of b cover the primes of q and meet in the primes of gcd a b. -/
theorem vdq_pf_union_inter {a b q : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : Nat.lcm a b = q) :
    a.primeFactors ∪ b.primeFactors = q.primeFactors ∧
      a.primeFactors ∩ b.primeFactors = (Nat.gcd a b).primeFactors := by
  have hl0 : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have hg0 : Nat.gcd a b ≠ 0 := Nat.gcd_ne_zero_left ha0
  refine ⟨?_, (Nat.primeFactors_gcd ha0 hb0).symm⟩
  rw [← Nat.primeFactors_mul ha0 hb0, ← Nat.gcd_mul_lcm a b, Nat.primeFactors_mul hg0 hl0,
    union_eq_right.mpr (Nat.primeFactors_mono (dvd_trans (Nat.gcd_dvd_left a b)
      (Nat.dvd_lcm_left a b)) hl0), hab]

/- Helper: for squarefree q the pairs a, b of divisors of q with lcm a b equal to q inject
into pairs (A, C) where A is the set of primes of a and C is the set of primes of gcd a b,
so there are at most the sum over A of 2 to the size of A, which is 3 to the omega of q. -/
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

/- Helper: page 15, h of a square free d is the product of h of p over the primes of d. -/
theorem vdq_h_eq_prod {w d : ℕ} (hd : Squarefree d) :
    envelopingH w d = ∏ p ∈ d.primeFactors, envelopingH w p := by
  unfold envelopingH
  rw [if_pos hd]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [if_pos hpp.squarefree, hpp.primeFactors, prod_singleton]

/- Helper: page 15 to 16, at a prime p above w at least 5, h of p lies in 0, 2/5 and h of
p is at most 7/5 times g of p. -/
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

/- Helper: reference 18 formula 4.1.18, termwise: for a, b dividing q with lcm a b equal
to q, the kernel term is at most h of q, since the absolute product is at most the product
of one over h of p over the primes of gcd a b. -/
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

theorem vdq_local_factor {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then
          envelopingH w a * envelopingH w b *
            |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
        else 0) ≤
      (21 / 5 : ℝ) ^ q.primeFactors.card * envelopingDensity w q := by
  have hsq : Squarefree q := (enveloping_divisor_support (J := 0) hw hq).1
  have hq0 : q ≠ 0 := hsq.ne_zero
  -- Restrict the sum to pairs with lcm equal to q.
  have hsum_le : ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
      (if Nat.lcm a b = q then envelopingH w a * envelopingH w b *
        |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)| else 0) ≤
    ∑ x ∈ (q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q),
      envelopingH w q := by
    have h1 : ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then envelopingH w a * envelopingH w b *
          |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)| else 0) =
      ∑ x ∈ (q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q),
        (if Nat.lcm x.1 x.2 = q then envelopingH w x.1 * envelopingH w x.2 *
          |∏ p ∈ (Nat.gcd x.1 x.2).primeFactors, (1 - 1 / envelopingH w p)| else 0) := by
      apply Finset.sum_bij (fun (a : ℕ) (b : ℕ) => ⟨a, b⟩)
      · intro a ha b hb _ _
        simp only [mem_product, mem_filter, mem_sigma, Nat.mem_divisors, Set.mem_setOf_eq]
        <;> constructor <;> simp_all [Nat.mem_divisors]
        <;> (try { contradiction })
      · intro x hx y hy hxy
        simp only [mem_product, mem_filter, mem_sigma, Nat.mem_divisors, Set.mem_setOf_eq] at hx hy hxy
        simp_all [Prod.mk.injEq]
      · intro x hx
        simp only [mem_product, mem_filter, mem_sigma, Nat.mem_divisors, Set.mem_setOf_eq]
        constructor <;> simp_all [Nat.mem_divisors]
    rw [h1]
    apply sum_le_sum
    intro x hx
    simp only [mem_filter, mem_product, Nat.mem_divisors, Set.mem_setOf_eq] at hx
    have ha : x.1 ∣ q := hx.1.1
    have hb : x.2 ∣ q := hx.1.2
    have hab : Nat.lcm x.1 x.2 = q := hx.2
    have ha0 : x.1 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ ha))
    have hb0 : x.2 ≠ 0 := fun h => hq0 (Nat.eq_zero_of_zero_dvd (h ▸ hb))
    have hterm := vdq_term_le hw hq ha hb hab
    split_ifs at hx ⊢ <;>
      (try { contradiction }) <;>
      (try { linarith }) <;>
      (try {
        have h₁ : 0 ≤ envelopingH w x.1 := envelopingH_nonneg w x.1
        have h₂ : 0 ≤ envelopingH w x.2 := envelopingH_nonneg w x.2
        nlinarith [hterm]
      }) <;>
      (try {
        have h₁ : 0 ≤ envelopingH w x.1 := envelopingH_nonneg w x.1
        have h₂ : 0 ≤ envelopingH w x.2 := envelopingH_nonneg w x.2
        nlinarith [abs_nonneg (∏ p ∈ (Nat.gcd x.1 x.2).primeFactors, (1 - 1 / envelopingH w p))]
      })
  
  -- Bound the number of pairs with lcm equal to q by 3^omega(q).
  have hcard : (∑ x ∈ (q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q),
      envelopingH w q : ℝ) =
      ((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card * envelopingH w q := by
    simp [sum_const, nsmul_eq_mul]
    <;> ring
  have hcard_le : ((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card ≤
      3 ^ q.primeFactors.card := vdq_lcm_pairs_card hsq
  
  -- Bound envelopingH w q by (7/5)^omega(q) * envelopingDensity w q.
  have hH_bound : envelopingH w q ≤ (7 / 5 : ℝ) ^ q.primeFactors.card * envelopingDensity w q := by
    have hsq' : Squarefree q := hsq
    rw [vdq_h_eq_prod hsq', envelopingDensity, ← prod_const, ← prod_mul_distrib]
    apply Finset.prod_le_prod₀ (fun p _ => envelopingH_nonneg w p)
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := (vdq_local_bounds hw hpp
      (efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hq))).2.2
    unfold envelopingDensity at this
    rwa [hpp.primeFactors, prod_singleton] at this
  
  -- Combine: total ≤ card * H_bound ≤ 3^omega * (7/5)^omega * density = (21/5)^omega * density.
  calc
    ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
      (if Nat.lcm a b = q then envelopingH w a * envelopingH w b *
        |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)| else 0) ≤
        (∑ x ∈ (q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q),
          envelopingH w q : ℝ) := hsum_le
    _ = ((q.divisors ×ˢ q.divisors).filter (fun x => Nat.lcm x.1 x.2 = q)).card * envelopingH w q := by rw [hcard]
    _ ≤ (3 ^ q.primeFactors.card : ℝ) * envelopingH w q := by
      exact_mod_cast (mul_le_mul_of_nonneg_right hcard_le (envelopingH_nonneg w q))
    _ ≤ (3 ^ q.primeFactors.card : ℝ) * ((7 / 5 : ℝ) ^ q.primeFactors.card *
        envelopingDensity w q) := by
      exact mul_le_mul_of_nonneg_right (by positivity) hH_bound
    _ = (21 / 5 : ℝ) ^ q.primeFactors.card * envelopingDensity w q := by
      rw [← mul_assoc, ← mul_pow]
      <;> norm_num
      <;> ring_nf
      <;> field_simp
      <;> ring_nf

/-- Page 15: the diagonal mass of h over n dividing P of z with n at most z is at most G 1
of z, since each such n is one of the delta in the sum defining G 1 of z. -/
theorem vdq_truncated_mass (w : ℕ) {z : ℝ} (q : ℕ) :
    ∑ n ∈ ((envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q)).filter
        (fun n : ℕ => (n : ℝ) ≤ z), envelopingH w n ≤ envelopingG w 1 z := by
  unfold envelopingG
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_filter, Nat.mem_divisors] at hn
    obtain ⟨⟨⟨hdvd, hP⟩, -⟩, hnz⟩ := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hP (zero_dvd_iff.mp hdvd)
    simp only [mem_filter, mem_Icc, Nat.lcm_one_left]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hn0, ?_⟩, hnz⟩
    have hz0 : (0 : ℝ) ≤ z := le_trans (Nat.cast_nonneg n) hnz
    exact Nat.le_floor hnz
  · intro n _ _
    exact envelopingH_nonneg w n

/-- Page 16: the local density g of q is positive for q dividing P of z, since every prime
of q lies above w and so omega of p is 1 or 2. -/
theorem vdq_density_pos {w : ℕ} {z : ℝ} {q : ℕ} (hq : q ∣ envelopingPrimeProduct w z) :
    0 < envelopingDensity w q := by
  unfold envelopingDensity
  apply prod_pos
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  have hgt := efs_prime_gt hpp (dvd_trans hpq hq)
  have hom : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    split_ifs <;> omega
  have : (0 : ℝ) < envelopingOmega w p := by exact_mod_cast hom
  have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  positivity

/-- The kernel at n vanishes unless n is at most z, and is bounded by the absolute kernel. -/
theorem vdq_kernel_abs_le {w : ℕ} {z : ℝ} {q n : ℕ} :
    |∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
          envelopingH w a * envelopingH w b *
            ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
        else 0)| ≤
      if (n : ℝ) ≤ z then
        ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
          (if Nat.lcm a b = q then
            envelopingH w a * envelopingH w b *
              |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
          else 0)
      else 0 := by
  split_ifs with hnz
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
    split_ifs with h1 h2
    · rw [abs_mul, abs_mul, abs_of_nonneg (envelopingH_nonneg w a),
        abs_of_nonneg (envelopingH_nonneg w b)]
    · exact absurd h1.1 h2
    · rw [abs_zero]
      have := envelopingH_nonneg w a
      have := envelopingH_nonneg w b
      positivity
    · rw [abs_zero]
  · rw [abs_nonpos_iff]
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b _
    rw [ite_eq_right_iff]
    rintro ⟨-, h2, -⟩
    exfalso
    apply hnz
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors ha))
    have : n ≤ n * a := Nat.le_mul_of_pos_right n ha1
    have : (n : ℝ) ≤ ((n * a : ℕ) : ℝ) := by exact_mod_cast this
    linarith

/-- Assembly: the exact statement of `vdecay_quadratic_bound` with K equal to 21 over 5,
from the diagonalization leaf, the local factor leaf and the proved truncated mass bound. -/
theorem vdecay_quadratic_bound_of_leaves :
    type_of% @LeanLab.Teravainen2016.vdecay_quadratic_bound := by
  refine ⟨21 / 5, by norm_num, ?_⟩
  intro w hw z hz q hq
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  rw [vdq_selberg_diagonal hw5 hz hq]
  set U := ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then
          envelopingH w a * envelopingH w b *
            |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
        else 0) with hU
  have hg := vdq_density_pos hq
  have hG := envelopingG_one_le w hz
  have hG0 : 0 < envelopingG w 1 z := by linarith
  have hU0 : 0 ≤ U := by
    apply sum_nonneg; intro a _; apply sum_nonneg; intro b _
    split_ifs
    · have := envelopingH_nonneg w a
      have := envelopingH_nonneg w b
      positivity
    · exact le_refl 0
  have hloc := vdq_local_factor hw5 (z := z) hq
  rw [← hU] at hloc
  set S := (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q) with hS
  have hsum : |∑ n ∈ S, envelopingH w n *
      ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
          envelopingH w a * envelopingH w b *
            ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
        else 0)| ≤ envelopingG w 1 z * U := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ n ∈ S, (if (n : ℝ) ≤ z then envelopingH w n * U else 0) := by
          apply sum_le_sum
          intro n _
          rw [abs_mul, abs_of_nonneg (envelopingH_nonneg w n)]
          have hk := vdq_kernel_abs_le (w := w) (z := z) (q := q) (n := n)
          rw [← hU] at hk
          have hh := envelopingH_nonneg w n
          split_ifs at hk ⊢
          · exact mul_le_mul_of_nonneg_left hk hh
          · have : |∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
                (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                  envelopingH w a * envelopingH w b *
                    ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
                else 0)| = 0 := le_antisymm hk (abs_nonneg _)
            rw [this, mul_zero]
      _ = (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ z), envelopingH w n) * U := by
          rw [← sum_filter, sum_mul]
      _ ≤ envelopingG w 1 z * U :=
          mul_le_mul_of_nonneg_right (vdq_truncated_mass w q) hU0
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hg hG0)]
  calc 1 / (envelopingDensity w q * envelopingG w 1 z) * |_|
      ≤ 1 / (envelopingDensity w q * envelopingG w 1 z) * (envelopingG w 1 z * U) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = U / envelopingDensity w q := by field_simp
    _ ≤ (21 / 5 : ℝ) ^ q.primeFactors.card := by
        rw [div_le_iff₀ hg]; exact hloc

#print axioms vdq_truncated_mass
#print axioms vdq_density_pos
#print axioms vdq_kernel_abs_le
#print axioms vdecay_quadratic_bound_of_leaves

end LeanLab.Teravainen2016
