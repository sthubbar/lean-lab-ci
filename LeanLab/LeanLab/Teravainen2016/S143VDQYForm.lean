/-
P0076, Section 4, Proposition 4.1 v, page 16, citing Ramare and Ruzsa reference 18 formula
4.1.15. Split of the HARD leaf `vdq_y_collapse` of VDQSelbergDiagonal1122d.lean into four
leaves: the density step that turns g of lcm over q into one over g of q and g of gcd, the
expansion of the y sums and of one over g of gcd as a divisor sum of one over h, the local
evaluation of the Mobius coefficient prime by prime, and the reindexing of m1, m2 as n a, n b.
The assembly `vdq_y_collapse_of_leaves` has the identical statement of `vdq_y_collapse` and is
proved from the leaves. Checked numerically for w equal to 5 and z up to 23.5 in S143.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDQSelbergDiagonal1122d

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The local Mobius coefficient c of m1, m2 at level q: the sum over d1 dividing m1 and d2
dividing m2 with q dividing lcm d1 d2 of mu d1 mu d2 times the sum over t dividing gcd d1 d2
of one over h of t. -/
noncomputable def vdqC (w q m1 m2 : ℕ) : ℝ :=
  ∑ d1 ∈ m1.divisors, ∑ d2 ∈ m2.divisors,
    (if q ∣ Nat.lcm d1 d2 then
      (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
        ∑ t ∈ (Nat.gcd d1 d2).divisors, 1 / envelopingH w t
    else 0)

/-- Density step of reference 18 formula 4.1.15, proved in S143. Multiply out the factor
G_1, use g of lcm over q equal to g of lcm over g of q and g of lcm times g of gcd equal to
g d1 g d2, from `vdq_density_lcm_gcd`. When G_1 is 0 both sides are 0. -/
theorem s143_collapse_density_step {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) {q : ℕ}
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
      1 / (envelopingDensity w q * envelopingG w 1 z) *
        ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
                vdqY w z d1 * vdqY w z d2 / envelopingDensity w (Nat.gcd d1 d2)
            else 0) := by
  have hP0 := envelopingPrimeProduct_ne_zero w z
  have hPsq := vdq_primeProduct_squarefree w z
  by_cases hG : envelopingG w 1 z = 0
  · rw [hG, zero_mul, mul_zero, div_zero, zero_mul]
  have hgq : envelopingDensity w q ≠ 0 := (vdq_density_pos hq).ne'
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro d1 hd1
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro d2 hd2
  split_ifs with hql
  · have hd1P := Nat.dvd_of_mem_divisors hd1
    have hd2P := Nat.dvd_of_mem_divisors hd2
    have hlP : Nat.lcm d1 d2 ∣ envelopingPrimeProduct w z := Nat.lcm_dvd hd1P hd2P
    have hgP : Nat.gcd d1 d2 ∣ envelopingPrimeProduct w z := (Nat.gcd_dvd_left d1 d2).trans hd1P
    have hrP : Nat.lcm d1 d2 / q ∣ envelopingPrimeProduct w z :=
      (Nat.div_dvd_of_dvd hql).trans hlP
    have hd10 : d1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd1)
    have hd20 : d2 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd2)
    have hsplit : Nat.lcm d1 d2 / q * q = Nat.lcm d1 d2 := Nat.div_mul_cancel hql
    have hcop : Nat.Coprime (Nat.lcm d1 d2 / q) q :=
      Nat.coprime_of_squarefree_mul (by rw [hsplit]; exact hPsq.squarefree_of_dvd hlP)
    have hmul : envelopingDensity w (Nat.lcm d1 d2) =
        envelopingDensity w (Nat.lcm d1 d2 / q) * envelopingDensity w q := by
      conv_lhs => rw [← hsplit]
      unfold envelopingDensity
      rw [Nat.Coprime.primeFactors_mul hcop, prod_union hcop.disjoint_primeFactors]
    have hlg := vdq_density_lcm_gcd w hd10 hd20
    have g1 : envelopingDensity w d1 ≠ 0 := (vdq_density_pos hd1P).ne'
    have g2 : envelopingDensity w d2 ≠ 0 := (vdq_density_pos hd2P).ne'
    have gg : envelopingDensity w (Nat.gcd d1 d2) ≠ 0 := (vdq_density_pos hgP).ne'
    have gr : envelopingDensity w (Nat.lcm d1 d2 / q) =
        envelopingDensity w d1 * envelopingDensity w d2 /
          (envelopingDensity w (Nat.gcd d1 d2) * envelopingDensity w q) := by
      rw [← hlg, hmul]
      field_simp
    rw [gr]
    field_simp
  · simp

/-- For e dividing P of z with w at least 2, one over g of e is the sum over t dividing e of
one over h of t. -/
theorem s143_inv_density_sum {w : ℕ} (hw : 2 ≤ w) {z : ℝ} {e : ℕ}
    (he : e ∣ envelopingPrimeProduct w z) :
    1 / envelopingDensity w e = ∑ t ∈ e.divisors, 1 / envelopingH w t := by
  have hsq : Squarefree e := (vdq_primeProduct_squarefree w z).squarefree_of_dvd he
  set f : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors
      (fun p => ((p - envelopingOmega w p : ℕ) : ℝ) / envelopingOmega w p) with hf
  have hfe : ∀ t ∈ e.divisors, f t = 1 / envelopingH w t := by
    intro t ht
    have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ht)
    have hst : Squarefree t := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht)
    rw [hf, ArithmeticFunction.prodPrimeFactors_apply ht0, envelopingH, if_pos hst,
      one_div, ← prod_inv_distrib]
    apply prod_congr rfl
    intro p _
    rw [inv_div]
  rw [← sum_congr rfl hfe,
    ← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree
      hsq]
  unfold envelopingDensity
  rw [one_div, ← prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  have hpP : p ∈ (envelopingPrimeProduct w z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans he, envelopingPrimeProduct_ne_zero w z⟩
  have hpw := (envelopingPrimeProduct_factor hpP).1
  have hp1 : f p = ((p - envelopingOmega w p : ℕ) : ℝ) / envelopingOmega w p := by
    rw [hf, ArithmeticFunction.prodPrimeFactors_apply (Nat.prime_of_mem_primeFactors hp).ne_zero,
      (Nat.prime_of_mem_primeFactors hp).primeFactors, prod_singleton]
  rw [hp1]
  have hom1 : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega; split_ifs <;> omega
  have hom2 : envelopingOmega w p ≤ 2 := by
    unfold envelopingOmega; split_ifs <;> omega
  have hlt : envelopingOmega w p < p := by omega
  rw [Nat.cast_sub hlt.le]
  have h1 : (0 : ℝ) < envelopingOmega w p := by exact_mod_cast hom1
  field_simp
  ring

/-- Expansion step of reference 18 formula 4.1.15, proved in S143. Write each y sum as
the sum of h of m over the multiples m of d dividing P of z with m at most z, write one over
g of gcd d1 d2 as the sum over t dividing it of one over h of t, as in `vdq_inv_density_prime`
and `vdq_sum_divisors_H`, and exchange the order of summation. -/
theorem s143_collapse_expand {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
        ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
          (if q ∣ Nat.lcm d1 d2 then
            (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
              vdqY w z d1 * vdqY w z d2 / envelopingDensity w (Nat.gcd d1 d2)
          else 0) =
      ∑ m1 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
        ∑ m2 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
          envelopingH w m1 * envelopingH w m2 * vdqC w q m1 m2 := by
  have hP0 := envelopingPrimeProduct_ne_zero w z
  set D := (envelopingPrimeProduct w z).divisors with hD
  set Dz := D.filter (fun m : ℕ => (m : ℝ) ≤ z) with hDz
  have hY : ∀ d, vdqY w z d = ∑ m ∈ Dz, if d ∣ m then envelopingH w m else 0 := by
    intro d
    unfold vdqY
    rw [← hD, ← sum_filter, hDz, filter_filter]
    congr 1
    ext m
    simp only [mem_filter]
    tauto
  have hdiv : ∀ m ∈ Dz, ∀ F : ℕ → ℝ,
      ∑ d ∈ m.divisors, F d = ∑ d ∈ D, if d ∣ m then F d else 0 := by
    intro m hm F
    rw [← sum_filter]
    congr 1
    ext d
    rw [hDz, mem_filter, hD, Nat.mem_divisors] at hm
    rw [mem_filter, hD, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans hm.1.1, hP0⟩, h1⟩
    · rintro ⟨-, h1⟩
      exact ⟨h1, fun h => hP0 (zero_dvd_iff.mp (h ▸ hm.1.1))⟩
  have hLHS : ∀ d1 ∈ D, ∀ d2 ∈ D,
      (if q ∣ Nat.lcm d1 d2 then
        (ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
          vdqY w z d1 * vdqY w z d2 / envelopingDensity w (Nat.gcd d1 d2)
      else 0) =
      ∑ m1 ∈ Dz, ∑ m2 ∈ Dz,
        (if q ∣ Nat.lcm d1 d2 ∧ d1 ∣ m1 ∧ d2 ∣ m2 then
          envelopingH w m1 * envelopingH w m2 *
            ((ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
              ∑ t ∈ (Nat.gcd d1 d2).divisors, 1 / envelopingH w t)
        else 0) := by
    intro d1 hd1 d2 hd2
    have hgP : Nat.gcd d1 d2 ∣ envelopingPrimeProduct w z :=
      (Nat.gcd_dvd_left d1 d2).trans (Nat.dvd_of_mem_divisors hd1)
    rw [← s143_inv_density_sum (by omega) hgP, hY, hY]
    split_ifs with hq'
    · rw [div_eq_mul_one_div, mul_assoc, mul_assoc,
        show ∀ a b A B c : ℝ, a * b * (A * (B * c)) = (A * B) * (a * b * c) from
          fun _ _ _ _ _ => by ring, sum_mul_sum, sum_mul]
      apply sum_congr rfl
      intro m1 _
      rw [sum_mul]
      apply sum_congr rfl
      intro m2 _
      by_cases h1 : d1 ∣ m1 <;> by_cases h2 : d2 ∣ m2 <;> simp [h1, h2, hq'] <;> ring
    · simp [hq']
  have hRHS : ∀ m1 ∈ Dz, ∀ m2 ∈ Dz,
      envelopingH w m1 * envelopingH w m2 * vdqC w q m1 m2 =
      ∑ d1 ∈ D, ∑ d2 ∈ D,
        (if q ∣ Nat.lcm d1 d2 ∧ d1 ∣ m1 ∧ d2 ∣ m2 then
          envelopingH w m1 * envelopingH w m2 *
            ((ArithmeticFunction.moebius d1 : ℝ) * (ArithmeticFunction.moebius d2 : ℝ) *
              ∑ t ∈ (Nat.gcd d1 d2).divisors, 1 / envelopingH w t)
        else 0) := by
    intro m1 hm1 m2 hm2
    unfold vdqC
    rw [hdiv m1 hm1, mul_sum]
    apply sum_congr rfl
    intro d1 _
    by_cases h1 : d1 ∣ m1
    · rw [if_pos h1, hdiv m2 hm2, mul_sum]
      apply sum_congr rfl
      intro d2 _
      by_cases h2 : d2 ∣ m2 <;> by_cases hq' : q ∣ Nat.lcm d1 d2 <;> simp [h1, h2, hq']
    · rw [if_neg h1, mul_zero]
      symm
      apply sum_eq_zero
      intro d2 _
      simp [h1]
  rw [sum_congr rfl (fun d1 hd1 => sum_congr rfl (fun d2 hd2 => hLHS d1 hd1 d2 hd2)),
    sum_congr rfl (fun m1 hm1 => sum_congr rfl (fun m2 hm2 => hRHS m1 hm1 m2 hm2))]
  conv_lhs => enter [2, d1]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro m1 _
  conv_lhs => enter [2, d1]; rw [sum_comm]
  rw [sum_comm]

/-- LEAF: local evaluation of the Mobius coefficient, reference 18 formula 4.1.15, class HARD.
All of q, m1, m2 divide P of z, so the sum factors over primes. A prime of m1 or m2 outside q
must divide both and gives one over h of p; a prime of q must divide m1 or m2 and gives minus 1
if it divides only one and minus 1 minus 1 over h of p if it divides both. With a and b the
q parts of m1 and m2, the coefficient vanishes unless m1 over a equals m2 over b and lcm a b
equals q. -/
theorem s143_local_coeff {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q m1 m2 : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) (h1 : m1 ∣ envelopingPrimeProduct w z)
    (h2 : m2 ∣ envelopingPrimeProduct w z) :
    envelopingH w m1 * envelopingH w m2 * vdqC w q m1 m2 =
      if m1 / Nat.gcd m1 q = m2 / Nat.gcd m2 q ∧ Nat.lcm (Nat.gcd m1 q) (Nat.gcd m2 q) = q then
        (-1 : ℝ) ^ q.primeFactors.card * (envelopingH w (m1 / Nat.gcd m1 q) *
          (envelopingH w (Nat.gcd m1 q) * envelopingH w (Nat.gcd m2 q) *
            ∏ p ∈ (Nat.gcd (Nat.gcd m1 q) (Nat.gcd m2 q)).primeFactors,
              (1 - 1 / envelopingH w p)))
      else 0 := by
  sorry

/-- Reindexing step of reference 18 formula 4.1.15, proved in S143. The pairs m1, m2 of
divisors of P of z at most z with m1 over gcd m1 q equal to m2 over gcd m2 q and the q parts
of lcm q are exactly n a, n b with n dividing P coprime to q and a, b dividing q with lcm a b
equal to q, through n equal to m1 over gcd m1 q, a equal to gcd m1 q, b equal to gcd m2 q. -/
theorem s143_collapse_reindex {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    ∑ m1 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
        ∑ m2 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
          (if m1 / Nat.gcd m1 q = m2 / Nat.gcd m2 q ∧
              Nat.lcm (Nat.gcd m1 q) (Nat.gcd m2 q) = q then
            (-1 : ℝ) ^ q.primeFactors.card * (envelopingH w (m1 / Nat.gcd m1 q) *
              (envelopingH w (Nat.gcd m1 q) * envelopingH w (Nat.gcd m2 q) *
                ∏ p ∈ (Nat.gcd (Nat.gcd m1 q) (Nat.gcd m2 q)).primeFactors,
                  (1 - 1 / envelopingH w p)))
          else 0) =
      (-1 : ℝ) ^ q.primeFactors.card *
        ∑ n ∈ (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q),
          envelopingH w n *
            ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
              (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                envelopingH w a * envelopingH w b *
                  ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
              else 0) := by
  have hP0 := envelopingPrimeProduct_ne_zero w z
  have hPsq := vdq_primeProduct_squarefree w z
  have hq0 : q ≠ 0 := fun h => hP0 (zero_dvd_iff.mp (h ▸ hq))
  have hcopdiv : ∀ m, m ∣ envelopingPrimeProduct w z → Nat.Coprime (m / Nat.gcd m q) q := by
    intro m hm
    have hg : Nat.gcd m q ∣ m := Nat.gcd_dvd_left m q
    have hsplit : Nat.gcd m q * (m / Nat.gcd m q) = m := Nat.mul_div_cancel' hg
    have hc : Nat.Coprime (Nat.gcd m q) (m / Nat.gcd m q) :=
      Nat.coprime_of_squarefree_mul (by rw [hsplit]; exact hPsq.squarefree_of_dvd hm)
    apply Nat.coprime_of_dvd
    intro p hp hp1 hp2
    have hpm : p ∣ m := hp1.trans (Nat.div_dvd_of_dvd hg)
    have hpg : p ∣ Nat.gcd m q := Nat.dvd_gcd hpm hp2
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpg hc) hp1)
  have key :
      ∑ x ∈ ((envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z) ×ˢ
          (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z)).filter
          (fun x : ℕ × ℕ => x.1 / Nat.gcd x.1 q = x.2 / Nat.gcd x.2 q ∧
            Nat.lcm (Nat.gcd x.1 q) (Nat.gcd x.2 q) = q),
        (-1 : ℝ) ^ q.primeFactors.card * (envelopingH w (x.1 / Nat.gcd x.1 q) *
          (envelopingH w (Nat.gcd x.1 q) * envelopingH w (Nat.gcd x.2 q) *
            ∏ p ∈ (Nat.gcd (Nat.gcd x.1 q) (Nat.gcd x.2 q)).primeFactors,
              (1 - 1 / envelopingH w p))) =
      ∑ y ∈ ((envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q) ×ˢ
          (q.divisors ×ˢ q.divisors)).filter
          (fun y : ℕ × ℕ × ℕ => Nat.lcm y.2.1 y.2.2 = q ∧ ((y.1 * y.2.1 : ℕ) : ℝ) ≤ z ∧
            ((y.1 * y.2.2 : ℕ) : ℝ) ≤ z),
        (-1 : ℝ) ^ q.primeFactors.card * (envelopingH w y.1 *
          (envelopingH w y.2.1 * envelopingH w y.2.2 *
            ∏ p ∈ (Nat.gcd y.2.1 y.2.2).primeFactors, (1 - 1 / envelopingH w p))) := by
    apply sum_nbij' (fun x => (x.1 / Nat.gcd x.1 q, Nat.gcd x.1 q, Nat.gcd x.2 q))
      (fun y => (y.1 * y.2.1, y.1 * y.2.2))
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_filter, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨⟨⟨h1P, -⟩, h1z⟩, ⟨⟨h2P, -⟩, h2z⟩⟩, hn, hl⟩ := hx
      have e1 : x.1 / Nat.gcd x.1 q * Nat.gcd x.1 q = x.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      have e2 : x.1 / Nat.gcd x.1 q * Nat.gcd x.2 q = x.2 := by
        rw [hn]; exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      refine ⟨⟨⟨⟨(Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)).trans h1P, hP0⟩, hcopdiv _ h1P⟩,
        ⟨Nat.gcd_dvd_right _ _, hq0⟩, ⟨Nat.gcd_dvd_right _ _, hq0⟩⟩, hl, ?_, ?_⟩
      · rw [e1]; exact h1z
      · rw [e2]; exact h2z
    · intro y hy
      simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_filter, Nat.mem_divisors] at hy ⊢
      obtain ⟨⟨⟨⟨hnP, -⟩, hnq⟩, ⟨haq, -⟩, ⟨hbq, -⟩⟩, hl, haz, hbz⟩ := hy
      have ga : Nat.gcd (y.1 * y.2.1) q = y.2.1 := by
        rw [Nat.Coprime.gcd_mul_left_cancel _ hnq]; exact Nat.gcd_eq_left haq
      have gb : Nat.gcd (y.1 * y.2.2) q = y.2.2 := by
        rw [Nat.Coprime.gcd_mul_left_cancel _ hnq]; exact Nat.gcd_eq_left hbq
      have ha0 : 0 < y.2.1 := Nat.pos_of_ne_zero (fun h => hq0 (zero_dvd_iff.mp (h ▸ haq)))
      have hb0 : 0 < y.2.2 := Nat.pos_of_ne_zero (fun h => hq0 (zero_dvd_iff.mp (h ▸ hbq)))
      refine ⟨⟨⟨⟨?_, hP0⟩, haz⟩, ⟨?_, hP0⟩, hbz⟩, ?_, ?_⟩
      · exact (hnq.coprime_dvd_right haq).mul_dvd_of_dvd_of_dvd hnP (haq.trans hq)
      · exact (hnq.coprime_dvd_right hbq).mul_dvd_of_dvd_of_dvd hnP (hbq.trans hq)
      · rw [ga, gb, Nat.mul_div_cancel _ ha0, Nat.mul_div_cancel _ hb0]
      · rw [ga, gb]; exact hl
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_filter, Nat.mem_divisors] at hx
      obtain ⟨-, hn, -⟩ := hx
      ext
      · exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      · show x.1 / Nat.gcd x.1 q * Nat.gcd x.2 q = x.2
        rw [hn]; exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    · intro y hy
      simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_filter, Nat.mem_divisors] at hy
      obtain ⟨⟨⟨⟨-, -⟩, hnq⟩, ⟨haq, -⟩, ⟨hbq, -⟩⟩, -, -, -⟩ := hy
      have ga : Nat.gcd (y.1 * y.2.1) q = y.2.1 := by
        rw [Nat.Coprime.gcd_mul_left_cancel _ hnq]; exact Nat.gcd_eq_left haq
      have gb : Nat.gcd (y.1 * y.2.2) q = y.2.2 := by
        rw [Nat.Coprime.gcd_mul_left_cancel _ hnq]; exact Nat.gcd_eq_left hbq
      have ha0 : 0 < y.2.1 := Nat.pos_of_ne_zero (fun h => hq0 (zero_dvd_iff.mp (h ▸ haq)))
      show ((y.1 * y.2.1) / Nat.gcd (y.1 * y.2.1) q, Nat.gcd (y.1 * y.2.1) q,
        Nat.gcd (y.1 * y.2.2) q) = y
      rw [ga, gb, Nat.mul_div_cancel _ ha0]
    · intro x _
      rfl
  simp only [sum_filter, sum_product] at key ⊢
  rw [key, mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs
  · rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro a _
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  · simp

/-- Assembly: the statement of `vdq_y_collapse` from the four leaves above. -/
theorem vdq_y_collapse_of_leaves :
    type_of% @LeanLab.Teravainen2016.vdq_y_collapse := by
  intro w hw z hz q hq
  rw [s143_collapse_density_step hw hz hq, s143_collapse_expand hw hq]
  have hloc : ∀ m1 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
      ∀ m2 ∈ (envelopingPrimeProduct w z).divisors.filter (fun m : ℕ => (m : ℝ) ≤ z),
        envelopingH w m1 * envelopingH w m2 * vdqC w q m1 m2 =
          if m1 / Nat.gcd m1 q = m2 / Nat.gcd m2 q ∧
              Nat.lcm (Nat.gcd m1 q) (Nat.gcd m2 q) = q then
            (-1 : ℝ) ^ q.primeFactors.card * (envelopingH w (m1 / Nat.gcd m1 q) *
              (envelopingH w (Nat.gcd m1 q) * envelopingH w (Nat.gcd m2 q) *
                ∏ p ∈ (Nat.gcd (Nat.gcd m1 q) (Nat.gcd m2 q)).primeFactors,
                  (1 - 1 / envelopingH w p)))
          else 0 := by
    intro m1 hm1 m2 hm2
    exact s143_local_coeff hw hq (Nat.dvd_of_mem_divisors (mem_filter.mp hm1).1)
      (Nat.dvd_of_mem_divisors (mem_filter.mp hm2).1)
  rw [sum_congr rfl (fun m1 hm1 => sum_congr rfl (fun m2 hm2 => hloc m1 hm1 m2 hm2)),
    s143_collapse_reindex hw hq]
  ring

#print axioms s143_collapse_density_step
#print axioms s143_inv_density_sum
#print axioms s143_collapse_expand
#print axioms s143_collapse_reindex
#print axioms vdq_y_collapse_of_leaves

end LeanLab.Teravainen2016
