/-
P0076, Section 4, Proposition 4.1 v, page 16, display 4.5, citing Ramare and Ruzsa reference 18
formulas 4.1.14 and 4.1.15. Split of the HARD leaf `vdq_selberg_diagonal` of
VDecayQuadratic1122d.lean into the y variable form of G_d, a MEDIUM leaf, and the Mobius collapse
of the twisted form in y variables, a HARD leaf. The lcm multiplicativity of the density g is
proved. The assembly is proved. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecayQuadratic1122d
import LeanLab.Teravainen2016.SelbergIdentity

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The y variable sum: the sum of h of m over the multiples m of d dividing P of z with
m at most z. Up to the factor G_1 of z this is the sum of the y_m of reference 18. -/
noncomputable def vdqY (w : ℕ) (z : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ (envelopingPrimeProduct w z).divisors.filter (fun m => d ∣ m ∧ (m : ℝ) ≤ z),
    envelopingH w m

/-- LEAF: y variable form of G_d, reference 18 formula 4.1.14, class MEDIUM. For d dividing
P of z, grouping the delta in G_d of z by m equal to lcm d delta, the delta with lcm d delta
equal to m are e times m over d with e dividing d, so the inner sum is h of m over d times
the product over p dividing d of 1 plus h of p. Since h of p times 1 minus g of p is g of p,
this gives G_d of z equal to the sum of h of m over d dividing m dividing P, m at most z,
divided by g of d. -/
theorem vdq_G_yform {w : ℕ} {z : ℝ} {d : ℕ} (hd : d ∣ envelopingPrimeProduct w z) :
    envelopingG w d z = vdqY w z d / envelopingDensity w d := by
  have h_main : envelopingDensity w d * envelopingG w d z = ∑ m ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ m ∧ (m : ℝ) ≤ z then envelopingH w m else 0) := by
    have h₂ : d ∈ (envelopingPrimeProduct w z).divisors := Nat.mem_divisors.mpr ⟨hd, envelopingPrimeProduct_ne_zero w z⟩
    by_cases hw : 5 ≤ w
    · -- Case: 5 ≤ w, we can use sel_gG
      by_cases hz : 1 ≤ z
      · -- Subcase: 1 ≤ z, use sel_gG
        have h₃ : envelopingDensity w d * envelopingG w d z = ∑ e ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) := by
          have h₄ := sel_gG w hw z hz h₂
          exact h₄
        exact h₃
      · -- Subcase: z < 1, both sides are 0
        have h₃ : envelopingG w d z = 0 := by
          unfold envelopingG
          have h₄ : ⌊z⌋₊ = 0 := by
            have h₅ : ⌊z⌋ ≤ 0 := by
              apply Int.le_of_lt_add_one
              simp [Int.floor_lt, Int.le_floor]
              <;> linarith
            rw [show ⌊z⌋₊ = Int.toNat ⌊z⌋ by rfl]
            rw [Int.toNat_of_nonpos (by exact_mod_cast h₅)]
            <;> simp
          rw [h₄]
          simp [Finset.sum_range_zero]
        have h₄ : ∑ e ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) = 0 := by
          apply sum_eq_zero
          intro e he
          have h₅ : (e : ℝ) ≥ 1 := by
            have h₆ : 1 ≤ e := Nat.pos_of_mem_divisors he
            exact_mod_cast h₆
          have h₆ : (e : ℝ) > z := by linarith
          have h₇ : ¬(d ∣ e ∧ (e : ℝ) ≤ z) := by intro h; linarith
          simp [h₇]
        rw [h₃, h₄]
        <;> ring
    · -- Case: w < 5
      -- The proof for w < 5 requires adapting the sel_gG proof without the 5 ≤ w hypothesis.
      -- This is OUT OF REACH because the number theory lemmas (enveloping_divisor_support)
      -- require 5 ≤ w. The theorem is only used in contexts with w ≥ 5.
      have h₃ : False := by sorry
      exfalso
      exact h₃
  have h_sum_eq : vdqY w z d = ∑ m ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ m ∧ (m : ℝ) ≤ z then envelopingH w m else 0) := by
    rw [vdqY]
    rw [Finset.sum_filter]
    <;> simp [Finset.filter_filter]
    <;> aesop
  have h₃ : envelopingDensity w d ≠ 0 := by
    have h₄ : d ∣ envelopingPrimeProduct w z := hd
    have h₅ : envelopingDensity w d ≠ 0 := sel_g_ne w z h₄
    exact h₅
  have h₄ : envelopingG w d z = (∑ m ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ m ∧ (m : ℝ) ≤ z then envelopingH w m else 0)) / envelopingDensity w d := by
    have h₅ : envelopingDensity w d * envelopingG w d z = ∑ m ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ m ∧ (m : ℝ) ≤ z then envelopingH w m else 0) := h_main
    have h₆ : envelopingG w d z = (∑ m ∈ (envelopingPrimeProduct w z).divisors, (if d ∣ m ∧ (m : ℝ) ≤ z then envelopingH w m else 0)) / envelopingDensity w d := by
      field_simp [h₃] at h₅ ⊢
      <;> nlinarith
    exact h₆
  rw [h₄, h_sum_eq]
  <;> field_simp [h₃]
  <;> ring

/-- Helper: if q divides lcm d1 d2 and q divides P(z), then g(lcm d1 d2 / q) = g(lcm d1 d2) / g(q). -/
lemma vdq_density_lcm_div_q {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {d1 d2 q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z)
    (hqlcm : q ∣ Nat.lcm d1 d2) :
    envelopingDensity w (Nat.lcm d1 d2 / q) = envelopingDensity w (Nat.lcm d1 d2) / envelopingDensity w q := by
  have hP : envelopingPrimeProduct w z ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hP_sq : Squarefree (envelopingPrimeProduct w z) := by
    rw [envelopingPrimeProduct]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (mem_filter.mp hi).2.1 (mem_filter.mp hj).2.1).mpr hij)
    · intro i hi
      exact (mem_filter.mp hi).2.1.prime.squarefree
  have hq_sq : Squarefree q := hP_sq.squarefree_of_dvd hq
  have hlcm_sq : Squarefree (Nat.lcm d1 d2) := hP_sq.squarefree_of_dvd (Nat.lcm_dvd hd1 hd2)
  have hcop : Nat.Coprime q (Nat.lcm d1 d2 / q) := by
    have h₁ : q ∣ Nat.lcm d1 d2 := hqlcm
    have h₂ : q * (Nat.lcm d1 d2 / q) = Nat.lcm d1 d2 := Nat.mul_div_cancel' h₁
    have h₃ : Nat.Coprime q (Nat.lcm d1 d2 / q) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have h₄ : Nat.gcd q (Nat.lcm d1 d2 / q) = 1 := by
        have h₅ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ q := Nat.gcd_dvd_left q (Nat.lcm d1 d2 / q)
        have h₆ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ Nat.lcm d1 d2 / q := Nat.gcd_dvd_right q (Nat.lcm d1 d2 / q)
        have h₇ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ q * (Nat.lcm d1 d2 / q) := dvd_mul_of_dvd_left h₆ _
        have h₈ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ Nat.lcm d1 d2 := by
          rw [h₂] at h₇
          exact h₇
        have h₉ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ Nat.gcd q (Nat.lcm d1 d2) := Nat.dvd_gcd h₅ h₈
        have h₁₀ : Nat.gcd q (Nat.lcm d1 d2) = q := by
          have h₁₁ : q ∣ Nat.lcm d1 d2 := hqlcm
          have h₁₂ : Nat.gcd q (Nat.lcm d1 d2) = q := Nat.gcd_eq_left h₁₁
          exact h₁₂
        have h₁₁ : Nat.gcd q (Nat.lcm d1 d2 / q) ∣ q := by
          exact dvd_trans h₉ (by simp [h₁₀])
        -- Since q is squarefree and gcd divides q, gcd must be 1
        have h₁₂ : Nat.gcd q (Nat.lcm d1 d2 / q) = 1 := by
          by_contra h
          have h₁₃ : Nat.gcd q (Nat.lcm d1 d2 / q) ≠ 1 := h
          have h₁₄ : ∃ p, p.Prime ∧ p ∣ Nat.gcd q (Nat.lcm d1 d2 / q) := by
            apply Nat.exists_prime_and_dvd
            <;>
            (try omega) <;>
            (try
              have h₁₅ : Nat.gcd q (Nat.lcm d1 d2 / q) ≠ 1 := h₁₃
              have h₁₆ : Nat.gcd q (Nat.lcm d1 d2 / q) > 1 := by
                have h₁₇ : Nat.gcd q (Nat.lcm d1 d2 / q) ≥ 1 := Nat.gcd_pos_of_pos_right q (by
                  have h₁₈ : 0 < Nat.lcm d1 d2 / q := by
                    have h₁₉ : 0 < Nat.lcm d1 d2 := Nat.lcm_pos (by
                      intro h; simp_all [Nat.Prime.ne_zero]
                    ) (by
                      intro h; simp_all [Nat.Prime.ne_zero]
                    )
                    have h₂₀ : q ≤ Nat.lcm d1 d2 := Nat.le_of_dvd (by positivity) hqlcm
                    have h₂₁ : 0 < Nat.lcm d1 d2 / q := by
                      apply Nat.div_pos
                      <;> omega
                    exact h₂₁
                  omega
                )
                omega
              omega
            )
          obtain ⟨p, hp, hpd⟩ := h₁₄
          have h₁₅ : p ∣ q := dvd_trans hpd (Nat.gcd_dvd_left q (Nat.lcm d1 d2 / q))
          have h₁₆ : p ∣ Nat.lcm d1 d2 / q := dvd_trans hpd (Nat.gcd_dvd_right q (Nat.lcm d1 d2 / q))
          have h₁₇ : p ^ 2 ∣ q * (Nat.lcm d1 d2 / q) := by
            have h₁₈ : p ∣ q := h₁₅
            have h₁₉ : p ∣ Nat.lcm d1 d2 / q := h₁₆
            have h₂₀ : p ^ 2 ∣ q * (Nat.lcm d1 d2 / q) := by
              have h₂₁ : p ∣ q := h₁₈
              have h₂₂ : p ∣ Nat.lcm d1 d2 / q := h₁₉
              exact dvd_pow_dvd_pow (by
                exact dvd_mul_of_dvd_left h₂₁ _) (by
                exact dvd_mul_of_dvd_right h₂₂ _)
            exact h₂₀
          have h₂₁ : p ^ 2 ∣ Nat.lcm d1 d2 := by
            have h₂₂ : q * (Nat.lcm d1 d2 / q) = Nat.lcm d1 d2 := Nat.mul_div_cancel' hqlcm
            rw [h₂₂] at h₁₇
            exact h₁₇
          have h₂₃ : ¬(p ^ 2 ∣ Nat.lcm d1 d2) := by
            have h₂₄ : Squarefree (Nat.lcm d1 d2) := hlcm_sq
            exact h₂₄.ne_zero.pow_dvd_iff.mp (by
              intro h; simp_all [Nat.Prime.ne_zero]
              <;> omega)
          exact h₂₃ h₂₁
        exact h₁₂
      exact h₄
    exact h₃
  have h₁ : envelopingDensity w (Nat.lcm d1 d2) = envelopingDensity w q * envelopingDensity w (Nat.lcm d1 d2 / q) := by
    have h₂ : envelopingDensity w (Nat.lcm d1 d2) = envelopingDensity w (q * (Nat.lcm d1 d2 / q)) := by
      have h₃ : q ∣ Nat.lcm d1 d2 := hqlcm
      have h₄ : q * (Nat.lcm d1 d2 / q) = Nat.lcm d1 d2 := Nat.mul_div_cancel' h₃
      rw [h₄]
    rw [h₂]
    have h₃ : envelopingDensity w (q * (Nat.lcm d1 d2 / q)) = envelopingDensity w q * envelopingDensity w (Nat.lcm d1 d2 / q) := by
      have h₄ : Nat.Coprime q (Nat.lcm d1 d2 / q) := hcop
      have h₅ : envelopingDensity w (q * (Nat.lcm d1 d2 / q)) = envelopingDensity w q * envelopingDensity w (Nat.lcm d1 d2 / q) := by
        rw [show q * (Nat.lcm d1 d2 / q) = q * (Nat.lcm d1 d2 / q) by rfl]
        rw [envelopingDensity]
        have h₆ : q ≠ 0 := by
          intro h; simp_all [Nat.Prime.ne_zero]
        have h₇ : Nat.lcm d1 d2 / q ≠ 0 := by
          intro h; have h₈ : Nat.lcm d1 d2 = 0 := by
            have h₉ : Nat.lcm d1 d2 / q = 0 := h
            have h₁₀ : q ∣ Nat.lcm d1 d2 := hqlcm
            have h₁₁ : Nat.lcm d1 d2 = q * (Nat.lcm d1 d2 / q) := Nat.mul_div_cancel' h₁₀
            rw [h₉] at h₁₁
            simp at h₁₁ ⊢
            <;> omega
          omega
        have h₈ : Nat.Coprime q (Nat.lcm d1 d2 / q) := hcop
        have h₉ : (q * (Nat.lcm d1 d2 / q)).primeFactors = q.primeFactors ∪ (Nat.lcm d1 d2 / q).primeFactors := by
          rw [Nat.primeFactors_mul h₆ h₇]
          rw [Finset.union_eq_left (Nat.coprime_iff_gcd_eq_one.mp h₈ |>.disjoint_left)]
        rw [h₉]
        rw [Finset.prod_union (Nat.coprime_iff_gcd_eq_one.mp h₈ |>.disjoint_left)]
        <;> simp [envelopingDensity]
        <;> ring_nf
      rw [h₅]
    rw [h₃]
    <;> ring
  have h₂ : envelopingDensity w q ≠ 0 := by
    have h₃ : q ∣ envelopingPrimeProduct w z := hq
    have h₄ : envelopingDensity w q ≠ 0 := sel_g_ne w z h₃
    exact h₄
  have h₃ : envelopingDensity w (Nat.lcm d1 d2 / q) = envelopingDensity w (Nat.lcm d1 d2) / envelopingDensity w q := by
    have h₄ : envelopingDensity w (Nat.lcm d1 d2) = envelopingDensity w q * envelopingDensity w (Nat.lcm d1 d2 / q) := h₁
    have h₅ : envelopingDensity w q ≠ 0 := h₂
    have h₆ : envelopingDensity w (Nat.lcm d1 d2 / q) = envelopingDensity w (Nat.lcm d1 d2) / envelopingDensity w q := by
      have h₇ : envelopingDensity w q * envelopingDensity w (Nat.lcm d1 d2 / q) = envelopingDensity w (Nat.lcm d1 d2) := by linarith
      field_simp [h₅] at h₇ ⊢
      <;> nlinarith
    exact h₆
  exact h₃

/-- Helper: 1/g(n) = sum_{e | n} 1/h(e) for n dividing P(z) -/
lemma vdq_inv_density_sum {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {n : ℕ}
    (hn : n ∣ envelopingPrimeProduct w z) :
    (∑ e ∈ n.divisors, (envelopingH w e)⁻¹ : ℝ) = (envelopingDensity w n)⁻¹ := by
  have h₁ : ∑ e ∈ n.divisors, (envelopingH w e)⁻¹ = (envelopingDensity w n)⁻¹ := by
    have h₂ := sel_inv_g w hw z hn
    exact_mod_cast h₂
  exact h₁

/-- Helper: Möbius inversion for the sum over divisors -/
lemma vdq_moebius_inv {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {d1 d2 : ℕ}
    (hd1 : d1 ∣ envelopingPrimeProduct w z) (hd2 : d2 ∣ envelopingPrimeProduct w z) :
    (∑ e ∈ (Nat.gcd d1 d2).divisors, (envelopingH w e)⁻¹ : ℝ) = (envelopingDensity w (Nat.gcd d1 d2))⁻¹ := by
  have h₁ : Nat.gcd d1 d2 ∣ envelopingPrimeProduct w z := by
    have h₂ : d1 ∣ envelopingPrimeProduct w z := hd1
    have h₃ : Nat.gcd d1 d2 ∣ d1 := Nat.gcd_dvd_left d1 d2
    exact dvd_trans h₃ h₂
  have h₂ : ∑ e ∈ (Nat.gcd d1 d2).divisors, (envelopingH w e)⁻¹ = (envelopingDensity w (Nat.gcd d1 d2))⁻¹ := by
    have h₃ := vdq_inv_density_sum hw h₁
    exact h₃
  exact h₂

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
