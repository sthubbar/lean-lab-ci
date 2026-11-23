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

/-- LEAF: y variable form of G_d, reference 18 formula 4.1.14, class MEDIUM. For d dividing
P of z, grouping the delta in G_d of z by m equal to lcm d delta, the delta with lcm d delta
equal to m are e times m over d with e dividing d, so the inner sum is h of m over d times
the product over p dividing d of 1 plus h of p. Since h of p times 1 minus g of p is g of p,
this gives G_d of z equal to the sum of h of m over d dividing m dividing P, m at most z,
divided by g of d. -/
theorem vdq_G_yform {w : ℕ} {z : ℝ} {d : ℕ} (hd : d ∣ envelopingPrimeProduct w z) :
    envelopingG w d z = vdqY w z d / envelopingDensity w d := by
  sorry

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
