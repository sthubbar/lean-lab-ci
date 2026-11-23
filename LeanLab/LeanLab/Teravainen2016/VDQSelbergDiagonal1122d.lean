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

/-- The prime product P of z is square free. -/
theorem vdq_primeProduct_squarefree (w : ℕ) (z : ℝ) :
    Squarefree (envelopingPrimeProduct w z) := by
  unfold envelopingPrimeProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (mem_filter.mp hi).2.1 (mem_filter.mp hj).2.1).mpr hij)
  · intro i hi
    exact (mem_filter.mp hi).2.1.prime.squarefree

/-- h is multiplicative on coprime arguments. -/
theorem vdq_H_mul_coprime (w : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    envelopingH w (a * b) = envelopingH w a * envelopingH w b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [envelopingH]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [envelopingH]
  unfold envelopingH
  by_cases hsa : Squarefree a
  · by_cases hsb : Squarefree b
    · rw [if_pos (Nat.squarefree_mul_iff.mpr ⟨hab, hsa, hsb⟩), if_pos hsa, if_pos hsb,
        Nat.Coprime.primeFactors_mul hab, prod_union hab.disjoint_primeFactors]
    · rw [if_neg (fun h => hsb (Nat.squarefree_mul_iff.mp h).2.2), if_neg hsb, mul_zero]
  · rw [if_neg (fun h => hsa (Nat.squarefree_mul_iff.mp h).2.1), if_neg hsa, zero_mul]

/-- h vanishes at every delta between 1 and z that does not divide P of z. -/
theorem vdq_H_eq_zero_of_not_dvd {w : ℕ} {z : ℝ} {δ : ℕ} (hδ1 : 1 ≤ δ) (hδz : (δ : ℝ) ≤ z)
    (hδ : ¬ δ ∣ envelopingPrimeProduct w z) : envelopingH w δ = 0 := by
  unfold envelopingH
  split_ifs with hsq
  · apply prod_eq_zero_iff.mpr
    by_contra hne
    push Not at hne
    apply hδ
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    unfold envelopingPrimeProduct
    apply prod_dvd_prod_of_subset
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ δ := Nat.le_of_dvd hδ1 hpd
    have hw : w < p := by
      by_contra hc
      push Not at hc
      apply hne p hp
      simp [envelopingOmega, hc]
    have hpz : (p : ℝ) ≤ z := le_trans (by exact_mod_cast hple) hδz
    simp only [mem_filter, mem_range]
    refine ⟨?_, hpp, hw, hpz⟩
    have := Nat.le_floor hpz
    omega
  · rfl

/-- For d dividing P of z with w at least 2, the sum of h over the divisors of d is h of d
over g of d. -/
theorem vdq_sum_divisors_H {w : ℕ} (hw : 2 ≤ w) {z : ℝ} {d : ℕ}
    (hd : d ∣ envelopingPrimeProduct w z) :
    ∑ e ∈ d.divisors, envelopingH w e = envelopingH w d / envelopingDensity w d := by
  have hsq : Squarefree d := (vdq_primeProduct_squarefree w z).squarefree_of_dvd hd
  set f : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors
      (fun p => (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ)) with hf
  have hfe : ∀ e ∈ d.divisors, f e = envelopingH w e := by
    intro e he
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
    have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
    rw [hf, ArithmeticFunction.prodPrimeFactors_apply he0, envelopingH, if_pos hse]
  rw [← sum_congr rfl hfe,
    ← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree
      hsq]
  unfold envelopingH envelopingDensity
  rw [if_pos hsq, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hpP : p ∈ (envelopingPrimeProduct w z).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hd, envelopingPrimeProduct_ne_zero w z⟩
  have hpw := (envelopingPrimeProduct_factor hpP).1
  have hp1 : f p = (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
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
  have h2 : (envelopingOmega w p : ℝ) < p := by exact_mod_cast hlt
  have h3 : (0 : ℝ) < (p : ℝ) - envelopingOmega w p := by linarith
  field_simp
  ring

/-- lcm of d and e times k is d times k when e divides d and k is coprime to d. -/
theorem vdq_lcm_mul {d e k : ℕ} (he : e ∣ d) (hk : Nat.Coprime d k) :
    Nat.lcm d (e * k) = d * k :=
  Nat.dvd_antisymm (Nat.lcm_dvd (Nat.dvd_mul_right d k) (Nat.mul_dvd_mul_right he k))
    (hk.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left _ _)
      ((Nat.dvd_mul_left k e).trans (Nat.dvd_lcm_right _ _)))

/-- Ramare and Ruzsa formula 4.1.14 for w at least 2: G_d of z is the y sum over g of d.
The leaf `vdq_G_yform` below has no hypothesis on w and fails for w at most 1 at d = 2, z = 2,
where h of 2 is 0 but g of 2 is 1. -/
theorem vdq_G_yform_of_two_le {w : ℕ} (hw : 2 ≤ w) {z : ℝ} {d : ℕ}
    (hd : d ∣ envelopingPrimeProduct w z) :
    envelopingG w d z = vdqY w z d / envelopingDensity w d := by
  have hg : envelopingDensity w d ≠ 0 := (vdq_density_pos hd).ne'
  have hsum := vdq_sum_divisors_H hw hd
  set P := envelopingPrimeProduct w z with hP
  have hP0 : P ≠ 0 := envelopingPrimeProduct_ne_zero w z
  have hPsq : Squarefree P := vdq_primeProduct_squarefree w z
  obtain ⟨d', hdd'⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; rw [zero_mul] at hdd'; exact hP0 hdd'
  have hd'0 : d' ≠ 0 := by rintro rfl; rw [mul_zero] at hdd'; exact hP0 hdd'
  have hcop : Nat.Coprime d d' := Nat.coprime_of_squarefree_mul (hdd' ▸ hPsq)
  set K := d'.divisors.filter (fun k => ((d * k : ℕ) : ℝ) ≤ z) with hK
  have hG : envelopingG w d z =
      ∑ δ ∈ P.divisors.filter (fun δ => (Nat.lcm d δ : ℝ) ≤ z), envelopingH w δ := by
    unfold envelopingG
    symm
    apply sum_subset_zero_on_sdiff
    · intro δ hδ
      rw [mem_filter, Nat.mem_divisors] at hδ
      have hδ0 : δ ≠ 0 := by rintro rfl; exact hP0 (zero_dvd_iff.mp hδ.1.1)
      have hle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      have hδz : (δ : ℝ) ≤ z := le_trans (by exact_mod_cast hle) hδ.2
      rw [mem_filter, mem_Icc]
      exact ⟨⟨Nat.pos_of_ne_zero hδ0, Nat.le_floor hδz⟩, hδ.2⟩
    · intro δ hδ
      rw [mem_sdiff, mem_filter, mem_Icc, mem_filter, Nat.mem_divisors] at hδ
      have hδ0 : δ ≠ 0 := by omega
      have hle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      exact vdq_H_eq_zero_of_not_dvd hδ.1.1.1 (le_trans (by exact_mod_cast hle) hδ.1.2)
        (fun hdv => hδ.2 ⟨⟨hdv, hP0⟩, hδ.1.2⟩)
    · intro δ _
      rfl
  have hL : ∑ δ ∈ P.divisors.filter (fun δ => (Nat.lcm d δ : ℝ) ≤ z), envelopingH w δ =
      (∑ e ∈ d.divisors, envelopingH w e) * ∑ k ∈ K, envelopingH w k := by
    rw [sum_mul_sum, ← sum_product']
    symm
    apply sum_nbij' (fun x => x.1 * x.2) (fun δ => (Nat.gcd δ d, Nat.gcd δ d'))
    · intro x hx
      rw [mem_product, hK, mem_filter, Nat.mem_divisors, Nat.mem_divisors] at hx
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hP0⟩, ?_⟩
      · rw [hdd']
        exact Nat.mul_dvd_mul hx.1.1 hx.2.1.1
      · rw [vdq_lcm_mul hx.1.1 (hcop.coprime_dvd_right hx.2.1.1)]
        exact hx.2.2
    · intro δ hδ
      rw [mem_filter, Nat.mem_divisors] at hδ
      have hδe : Nat.gcd δ d * Nat.gcd δ d' = δ := by
        rw [← Nat.Coprime.gcd_mul δ hcop, ← hdd']
        exact Nat.gcd_eq_left hδ.1.1
      rw [mem_product, hK, mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      refine ⟨⟨Nat.gcd_dvd_right δ d, hd0⟩, ⟨Nat.gcd_dvd_right δ d', hd'0⟩, ?_⟩
      have h2 := hδ.2
      rw [← hδe, vdq_lcm_mul (Nat.gcd_dvd_right δ d)
        (hcop.coprime_dvd_right (Nat.gcd_dvd_right δ d'))] at h2
      exact h2
    · intro x hx
      rw [mem_product, hK, mem_filter, Nat.mem_divisors, Nat.mem_divisors] at hx
      have hk : Nat.Coprime x.2 d := (hcop.coprime_dvd_right hx.2.1.1).symm
      have he : Nat.Coprime x.1 d' := hcop.coprime_dvd_left hx.1.1
      ext
      · show Nat.gcd (x.1 * x.2) d = x.1
        rw [Nat.Coprime.gcd_mul_right_cancel x.1 hk]
        exact Nat.gcd_eq_left hx.1.1
      · show Nat.gcd (x.1 * x.2) d' = x.2
        rw [Nat.Coprime.gcd_mul_left_cancel x.2 he]
        exact Nat.gcd_eq_left hx.2.1.1
    · intro δ hδ
      rw [mem_filter, Nat.mem_divisors] at hδ
      show Nat.gcd δ d * Nat.gcd δ d' = δ
      rw [← Nat.Coprime.gcd_mul δ hcop, ← hdd']
      exact Nat.gcd_eq_left hδ.1.1
    · intro x hx
      rw [mem_product, hK, mem_filter, Nat.mem_divisors, Nat.mem_divisors] at hx
      exact (vdq_H_mul_coprime w
        (Nat.Coprime.coprime_dvd_left hx.1.1 (hcop.coprime_dvd_right hx.2.1.1))).symm
  have hY : vdqY w z d = envelopingH w d * ∑ k ∈ K, envelopingH w k := by
    unfold vdqY
    rw [← hP, mul_sum]
    symm
    apply sum_nbij' (fun k => d * k) (fun m => m / d)
    · intro k hk
      rw [hK, mem_filter, Nat.mem_divisors] at hk
      rw [mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hP0⟩, Nat.dvd_mul_right d k, hk.2⟩
      rw [hdd']
      exact Nat.mul_dvd_mul_left d hk.1.1
    · intro m hm
      rw [mem_filter, Nat.mem_divisors] at hm
      obtain ⟨⟨hmP, -⟩, ⟨c, rfl⟩, hmz⟩ := hm
      rw [hK, mem_filter, Nat.mem_divisors,
        Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd0)]
      refine ⟨⟨?_, hd'0⟩, hmz⟩
      rw [hdd'] at hmP
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mp hmP
    · intro k _
      exact Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0)
    · intro m hm
      rw [mem_filter] at hm
      exact Nat.mul_div_cancel' hm.2.1
    · intro k hk
      rw [hK, mem_filter, Nat.mem_divisors] at hk
      exact (vdq_H_mul_coprime w (hcop.coprime_dvd_right hk.1.1)).symm
  rw [hG, hL, hY, hsum]
  ring

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
  have h1 := vdq_G_yform_of_two_le (by omega) (Nat.dvd_of_mem_divisors hd1)
  have h2 := vdq_G_yform_of_two_le (by omega) (Nat.dvd_of_mem_divisors hd2)
  unfold envelopingRho
  rw [h1, h2]

#print axioms vdq_density_lcm_gcd
#print axioms vdq_inv_density_prime
#print axioms vdq_G_yform_of_two_le
#print axioms vdq_selberg_diagonal_of_leaves

end LeanLab.Teravainen2016
