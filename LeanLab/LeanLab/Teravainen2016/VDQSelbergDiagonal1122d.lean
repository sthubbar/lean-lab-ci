/-
P0076, Section 4, Proposition 4.1 v, page 16, display 4.5, citing Ramare and Ruzsa reference 18
formulas 4.1.14 and 4.1.15. Split of the HARD leaf `vdq_selberg_diagonal` of
VDecayQuadratic1122d.lean into the y variable form of G_d, a MEDIUM leaf, and the Mobius collapse
of the twisted form in y variables, a HARD leaf. The lcm multiplicativity of the density g is
proved. The assembly is proved. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecayQuadratic1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The y variable sum: the sum of h of m over the multiples m of d dividing P of z with
m at most z. Up to the factor G_1 of z this is the sum of the y_m of reference 18. -/
noncomputable def vdqY (w : ℕ) (z : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ (envelopingPrimeProduct w z).divisors.filter (fun m => d ∣ m ∧ (m : ℝ) ≤ z),
    envelopingH w m

/-- Helper: envelopingH is multiplicative on coprime squarefree arguments. -/
lemma envelopingH_mul_coprime {w a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b) :
    envelopingH w (a * b) = envelopingH w a * envelopingH w b := by
  have h₁ : Squarefree (a * b) := Nat.squarefree_mul_iff.mpr ⟨ha, hb, hab⟩
  have h₂ : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    rw [Nat.primeFactors_mul hab]
  rw [h₁]
  simp only [envelopingH, h₁, if_pos, prod_union_inter, h₂, Finset.disjoint_left.mpr]
  <;> aesop

/-- Helper: envelopingDensity is multiplicative on coprime arguments. -/
lemma envelopingDensity_mul_coprime {w a b : ℕ} (hab : Nat.Coprime a b) :
    envelopingDensity w (a * b) = envelopingDensity w a * envelopingDensity w b := by
  have h₁ : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
    rw [Nat.primeFactors_mul hab]
  rw [envelopingDensity]
  simp only [h₁, prod_union_inter, Finset.disjoint_left.mpr]
  <;> aesop

/-- Helper: sum of envelopingH over divisors of a squarefree number dividing P_z. -/
lemma sum_envelopingH_divisors {w d : ℕ} (hd : Squarefree d) (hdP : ∀ p ∈ d.primeFactors, w < p) :
    ∑ e ∈ d.divisors, envelopingH w e = envelopingH w d / envelopingDensity w d := by
  have h₁ : ∀ p ∈ d.primeFactors, (1 : ℝ) + envelopingH w p = envelopingH w p / envelopingDensity w p := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpw : w < p := hdP p hp
    have h₂ := vdq_inv_density_prime w p (by linarith) hp'
    have h₃ : 1 / envelopingDensity w p = 1 + 1 / envelopingH w p := h₂
    have h₄ : 0 < envelopingH w p := by
      have h₅ : Squarefree p := hp'.squarefree
      have h₆ : 0 < envelopingH w p := by
        rw [envelopingH]
        simp [h₅, hp'.primeFactors, prod_singleton]
        have h₇ : 0 < (envelopingOmega w p : ℝ) := by
          have h₈ : 1 ≤ envelopingOmega w p := by
            unfold envelopingOmega; split_ifs <;> omega
          have h₉ : (0 : ℝ) < envelopingOmega w p := by exact_mod_cast h₈
          linarith
        have h₈ : 0 < (p : ℝ) - envelopingOmega w p := by
          have h₉ : envelopingOmega w p < p := by
            unfold envelopingOmega; split_ifs <;> omega
          have h₁₀ : (envelopingOmega w p : ℝ) < p := by exact_mod_cast h₉
          linarith
        positivity
      exact h₆
    have h₅ : 0 < envelopingDensity w p := by
      rw [envelopingDensity]
      simp [hp'.primeFactors, prod_singleton]
      have h₆ : 0 < (envelopingOmega w p : ℝ) := by
        have h₇ : 1 ≤ envelopingOmega w p := by
          unfold envelopingOmega; split_ifs <;> omega
        exact_mod_cast h₇
      positivity
    field_simp [h₄.ne', h₅.ne'] at h₃ ⊢
    <;> ring_nf at h₃ ⊢ <;> nlinarith
  -- Use the multiplicativity of envelopingH and envelopingDensity to prove the sum over divisors
  have h₂ : ∑ e ∈ d.divisors, envelopingH w e = ∏ p ∈ d.primeFactors, (1 + envelopingH w p) := by
    have h₃ : ∀ p ∈ d.primeFactors, p.Prime := by intro p hp; exact Nat.prime_of_mem_primeFactors hp
    -- Since d is squarefree, the sum over divisors of the multiplicative function envelopingH
    -- is the product over prime factors of (1 + envelopingH w p)
    have h₄ : ∑ e ∈ d.divisors, envelopingH w e = ∏ p ∈ d.primeFactors, (1 + envelopingH w p) := by
      -- Use the fact that envelopingH is multiplicative and d is squarefree
      have h₅ : ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → (∏ p in s, (1 + envelopingH w p) : ℝ) = ∑ e in (Nat.divisors (∏ p in s, p)), envelopingH w e := by
        intro s hs
        induction' s using Finset.induction_on with p s hps ih
        · simp [envelopingH]
        · rw [Finset.prod_insert hps, Finset.mul_sum, Finset.sum_mul, mul_comm]
          have h₆ : Nat.divisors (∏ q in s, q * p) = (Nat.divisors (∏ q in s, q)).image (fun d => d * p) ∪ Nat.divisors (∏ q in s, q) := by
            -- The divisors of n*p where p is prime not dividing n
            have h₇ : p.Prime := hs p (Finset.mem_insert_self p s)
            have h₈ : ¬p ∣ ∏ q in s, q := by
              intro h
              have h₉ : p ∣ ∏ q in s, q := h
              have h₁₀ : p ∈ s := by
                apply (Nat.prime_iff_prime_int.mp h₇).dvd_finsetProd_iff _ |>.mp h₉
                aesop
              contradiction
            have h₉ : Nat.Coprime p (∏ q in s, q) := by
              rw [Nat.coprime_comm]
              apply Nat.Prime.coprime_iff_not_dvd h₇ |>.mpr
              exact h₈
            rw [show (∏ q in s, q * p) = (∏ q in s, q) * p by ring]
            rw [Nat.divisors_mul h₉]
            <;> simp [Finset.ext_iff]
            <;> aesop
          rw [h₆]
          have h₇ : Disjoint ((Nat.divisors (∏ q in s, q)).image (fun d => d * p)) (Nat.divisors (∏ q in s, q)) := by
            rw [Finset.disjoint_left]
            intro x hx₁ hx₂
            simp only [Finset.mem_image, Finset.mem_singleton] at hx₁
            obtain ⟨d, hd, rfl⟩ := hx₁
            have h₈ : d * p ∈ Nat.divisors (∏ q in s, q) := hx₂
            have h₉ : d ∈ Nat.divisors (∏ q in s, q) := hd
            have h₁₀ : d * p ∣ ∏ q in s, q := Nat.dvd_of_mem_divisors h₈
            have h₁₁ : d ∣ ∏ q in s, q := Nat.dvd_of_mem_divisors h₉
            have h₁₂ : p ∣ ∏ q in s, q := dvd_of_mul_dvd_left (by
              have h₁₃ : 0 < d := Nat.pos_of_dvd_of_pos (by
                have h₁₄ : 0 < ∏ q in s, q := by
                  apply Finset.prod_pos
                  intro q hq
                  have h₁₅ : q.Prime := hs q hq
                  linarith [h₁₅.two_le]
                exact h₁₄) h₁₁) h₁₀
            have h₁₃ : p.Prime := hs p (Finset.mem_insert_self p s)
            have h₁₄ : p ∣ ∏ q in s, q := h₁₂
            have h₁₅ : p ∈ s := by
              apply (Nat.prime_iff_prime_int.mp h₁₃).dvd_finsetProd_iff _ |>.mp h₁₄
              aesop
            contradiction
          rw [Finset.sum_union h₇]
          have h₈ : ∑ x in (Nat.divisors (∏ q in s, q)).image (fun d => d * p), envelopingH w x = ∑ d in Nat.divisors (∏ q in s, q), envelopingH w (d * p) := by
            rw [Finset.sum_image]
            <;> aesop
          rw [h₈]
          have h₉ : ∀ d ∈ Nat.divisors (∏ q in s, q), envelopingH w (d * p) = envelopingH w d * envelopingH w p := by
            intro d hd
            have h₁₀ : d ∣ ∏ q in s, q := Nat.dvd_of_mem_divisors hd
            have h₁₁ : Squarefree d := by
              apply Nat.Squarefree.dvd
              have h₁₂ : Squarefree (∏ q in s, q) := by
                apply Finset.squarefree_prod_of_pairwise_isCoprime
                · intro q₁ hq₁ q₂ hq₂ hq₁₂
                  have h₁₃ := hs q₁ hq₁
                  have h₁₄ := hs q₂ hq₂
                  exact Nat.coprime_iff_isRelPrime.mp (Nat.coprime_primes h₁₃ h₁₄).mpr hq₁₂
                · intro q hq
                  exact (hs q hq).squarefree
              exact h₁₂
            have h₁₂ : Squarefree p := (hs p (Finset.mem_insert_self p s)).squarefree
            have h₁₃ : Nat.Coprime d p := by
              have h₁₄ : d ∣ ∏ q in s, q := h₁₀
              have h₁₅ : ¬p ∣ ∏ q in s, q := by
                intro h
                have h₁₆ : p ∈ s := by
                  apply (Nat.prime_iff_prime_int.mp (hs p (Finset.mem_insert_self p s))).dvd_finsetProd_iff _ |>.mp h
                  aesop
                contradiction
              have h₁₆ : ¬p ∣ d := by
                intro h
                have h₁₇ : p ∣ ∏ q in s, q := dvd_trans h h₁₄
                contradiction
              exact Nat.Prime.coprime_iff_not_dvd (hs p (Finset.mem_insert_self p s)) |>.mpr h₁₆
            have h₁₄ : envelopingH w (d * p) = envelopingH w d * envelopingH w p := by
              apply envelopingH_mul_coprime h₁₁ h₁₂ h₁₃
            exact h₁₄
          rw [h₈]
          apply Finset.sum_congr rfl
          intro d hd
          rw [h₉ d hd]
          <;> ring
        <;> simp_all [envelopingH]
        <;> norm_num
        <;> aesop
      have h₆ : ∑ e in Nat.divisors (∏ p in d.primeFactors, p), envelopingH w e = ∏ p in d.primeFactors, (1 + envelopingH w p) := by
        have h₇ : ∀ p ∈ d.primeFactors, p.Prime := by intro p hp; exact Nat.prime_of_mem_primeFactors hp
        have h₈ := h₅ d.primeFactors h₇
        simpa using h₈
      have h₇ : d = ∏ p in d.primeFactors, p := by
        have h₈ : Squarefree d := hd
        have h₉ : d = ∏ p in d.primeFactors, p := by
          rw [Nat.squarefree_iff_prod_primeFactors.mp h₈]
          <;> aesop
        exact h₉
      rw [h₇] at *
      exact h₆
    exact h₄
  have h₃ : (∏ p in d.primeFactors, (1 + envelopingH w p) : ℝ) = envelopingH w d / envelopingDensity w d := by
    have h₄ : ∀ p ∈ d.primeFactors, (1 + envelopingH w p : ℝ) = envelopingH w p / envelopingDensity w p := by
      intro p hp
      exact h₁ p hp
    calc
      (∏ p in d.primeFactors, (1 + envelopingH w p) : ℝ) = ∏ p in d.primeFactors, (envelopingH w p / envelopingDensity w p : ℝ) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [h₄ p hp]
      _ = (∏ p in d.primeFactors, envelopingH w p) / ∏ p in d.primeFactors, envelopingDensity w p := by
        rw [Finset.prod_div_distrib]
      _ = envelopingH w d / envelopingDensity w d := by
        have h₅ : Squarefree d := hd
        have h₆ : envelopingH w d = ∏ p in d.primeFactors, envelopingH w p := by
          rw [envelopingH]
          simp [h₅, if_pos]
          <;> aesop
        have h₇ : envelopingDensity w d = ∏ p in d.primeFactors, envelopingDensity w p := by
          rw [envelopingDensity]
          <;> simp [Nat.primeFactors_mul_coprime]
          <;> aesop
        rw [h₆, h₇]
  calc
    ∑ e ∈ d.divisors, envelopingH w e = ∏ p in d.primeFactors, (1 + envelopingH w p) := by rw [h₂]
    _ = envelopingH w d / envelopingDensity w d := by rw [h₃]

/-- Helper: For m dividing P_z with d ∣ m, the fiber of δ with lcm d δ = m is { (m/d) * e | e ∣ d }. -/
lemma lcm_fiber {w : ℕ} {z : ℝ} {d m : ℕ} (hd : d ∣ envelopingPrimeProduct w z) (hm : m ∣ envelopingPrimeProduct w z) (hdm : d ∣ m) :
    {δ : ℕ | 1 ≤ δ ∧ δ ≤ ⌊z⌋₊ ∧ Nat.lcm d δ ≤ z ∧ Nat.lcm d δ = m} =
    { (m / d) * e | e : ℕ, e ∣ d } := by
  sorry

/-- LEAF: y variable form of G_d, reference 18 formula 4.1.14, class MEDIUM. For d dividing
P of z, grouping the delta in G_d of z by m equal to lcm d delta, the delta with lcm d delta
equal to m are e times m over d with e dividing d, so the inner sum is h of m over d times
the product over p dividing d of 1 plus h of p. Since h of p times 1 minus g of p is g of p,
this gives G_d of z equal to the sum of h of m over d dividing m dividing P, m at most z,
divided by g of d. -/
theorem vdq_G_yform {w : ℕ} {z : ℝ} {d : ℕ} (hd : d ∣ envelopingPrimeProduct w z) :
    envelopingG w d z = vdqY w z d / envelopingDensity w d := by
  have h_d_sqfree : Squarefree d := by sorry
  have h_d_prime_factors_gt_w : ∀ p ∈ d.primeFactors, w < p := by sorry
  have h_sum_eq : envelopingG w d z = vdqY w z d / envelopingDensity w d := by sorry
  exact h_sum_eq

/-- LEAF: Mobius collapse of the twisted form in y variables, reference 18 formula 4.1.15,
class HARD. With rho_d written as mu of d over g of d times the y sum, expand g of lcm over q
as g d1 g d2 over g of gcd times g of q, write one over g of the gcd as the sum over e
dividing it of one over h of e, exchange the order and collapse the Mobius sums over d1, d2
one prime at a time, leaving the diagonal over n coprime to q and the kernel over a, b
dividing q with lcm a b equal to q. -/
theorem vdq_y_collapse {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    envelopingG w 1 z *
        ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              ((ArithmeticFunction.moebius d1 : ℝ) * (vdqY w z d1 / envelopingDensity w d1) /
                  envelopingG w 1 z) *
                ((ArithmeticFunction.moebius d2 : ℝ) * (vdqY w z d2 / envelopingDensity w d2) /
                  envelopingG w 1 z) *
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

/-- Page 16: the density g is multiplicative across lcm and gcd, g of lcm times g of gcd is
g d1 times g d2, for nonzero d1, d2, since the prime factors of lcm and gcd are the union and
the intersection. -/
theorem vdq_density_lcm_gcd (w : ℕ) {d1 d2 : ℕ} (h1 : d1 ≠ 0) (h2 : d2 ≠ 0) :
    envelopingDensity w (Nat.lcm d1 d2) * envelopingDensity w (Nat.gcd d1 d2) =
      envelopingDensity w d1 * envelopingDensity w d2 := by
  unfold envelopingDensity
  have hl : (Nat.lcm d1 d2).primeFactors = d1.primeFactors ∪ d2.primeFactors := by
    ext p
    simp only [mem_union, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, -⟩
      rcases (Nat.Prime.dvd_mul hp).mp (hpd.trans (Nat.lcm_dvd_mul d1 d2)) with h | h
      · exact Or.inl ⟨hp, h, h1⟩
      · exact Or.inr ⟨hp, h, h2⟩
    · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
      · exact ⟨hp, h.trans (Nat.dvd_lcm_left d1 d2), Nat.lcm_ne_zero h1 h2⟩
      · exact ⟨hp, h.trans (Nat.dvd_lcm_right d1 d2), Nat.lcm_ne_zero h1 h2⟩
  rw [hl, Nat.primeFactors_gcd h1 h2]
  exact prod_union_inter

/-- Page 16: the local identity behind the divisor sum for one over g, at a prime p above
w with w at least 5, one over g of p is 1 plus one over h of p. -/
theorem vdq_inv_density_prime {w p : ℕ} (hw : 5 ≤ w) (hp : p.Prime) (hpw : w < p) :
    1 / envelopingDensity w p = 1 + 1 / envelopingH w p := by
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega; split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega; split_ifs <;> omega
  have hlt : envelopingOmega w p < p := by omega
  unfold envelopingDensity envelopingH
  rw [if_pos hp.squarefree, hp.primeFactors, prod_singleton, prod_singleton,
    Nat.cast_sub hlt.le]
  have h1 : (0 : ℝ) < envelopingOmega w p := by exact_mod_cast hom1
  have h2 : (envelopingOmega w p : ℝ) < p := by exact_mod_cast hlt
  have h3 : (0 : ℝ) < (p : ℝ) - envelopingOmega w p := by linarith
  field_simp
  ring

/-- Assembly: `vdq_selberg_diagonal` from the y variable form of G_d and the collapse. -/
theorem vdq_selberg_diagonal_of_leaves :
    type_of% @LeanLab.Teravainen2016.vdq_selberg_diagonal := by
  intro w hw z hz q hq
  rw [← vdq_y_collapse hw hz hq]
  congr 1
  apply sum_congr rfl
  intro d1 hd1
  apply sum_congr rfl
  intro d2 hd2
  have h1 := vdq_G_yform (Nat.dvd_of_mem_divisors hd1)
  have h2 := vdq_G_yform (Nat.dvd_of_mem_divisors hd2)
  unfold envelopingRho
  rw [h1, h2]

#print axioms vdq_density_lcm_gcd
#print axioms vdq_inv_density_prime
#print axioms vdq_selberg_diagonal_of_leaves

end LeanLab.Teravainen2016
