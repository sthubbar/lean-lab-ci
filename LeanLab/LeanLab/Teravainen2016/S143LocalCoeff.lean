/-
P0076, Section 4, Proposition 4.1 v, citing Ramare and Ruzsa reference 18 formula 4.1.15.
S143 round 2 split of the HARD leaf `s143_local_coeff` of S143VDQYForm.lean into three leaves:
multiplicativity of `vdqC` over coprime splits of q, m1, m2; the evaluation at one prime; and
the induction over the prime factors of P of z, which takes the first two as hypotheses.
The assembly `s143_local_coeff_of_leaves` has the identical statement of `s143_local_coeff`.
All three leaves and the full statement were checked exactly in rationals by a python script
for w equal to 5 and P equal to 7 times 11 times 13. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.S143VDQYForm

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The multiplicativity statement for `vdqC` over coprime squarefree splits. -/
def VdqCMulStatement (w : ℕ) : Prop :=
  ∀ q1 q2 a1 a2 b1 b2 : ℕ, Squarefree (q1 * a1 * a2 * (q2 * b1 * b2)) →
    Nat.Coprime (q1 * a1 * a2) (q2 * b1 * b2) →
      vdqC w (q1 * q2) (a1 * b1) (a2 * b2) = vdqC w q1 a1 a2 * vdqC w q2 b1 b2

/-- The values of `vdqC` at a single prime p with each of q, m1, m2 equal to 1 or p. -/
def VdqCPrimeStatement (w : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    vdqC w 1 1 1 = 1 ∧ vdqC w 1 p 1 = 0 ∧ vdqC w 1 1 p = 0 ∧
      vdqC w 1 p p = 1 / envelopingH w p ∧
    vdqC w p 1 1 = 0 ∧ vdqC w p p 1 = -1 ∧ vdqC w p 1 p = -1 ∧
      vdqC w p p p = -1 + 1 / envelopingH w p

/-- LEAF: multiplicativity of the local coefficient over coprime splits, reference 18 formula
4.1.15, class MEDIUM. Divisors of a coprime product split as products, mu and one over h are
multiplicative, gcd and lcm split, and q1 q2 divides lcm iff each part divides its part. -/
theorem s143_sum_divisors_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (F : ℕ → ℝ) :
    ∑ d ∈ (m * n).divisors, F d = ∑ x ∈ m.divisors, ∑ y ∈ n.divisors, F (x * y) := by
  rw [hmn.divisors_mul, Finset.sum_map,
    ← Finset.sum_product (f := fun p : ℕ × ℕ => F (p.1 * p.2))]
  exact Finset.sum_attach (m.divisors ×ˢ n.divisors) (fun p => F (p.1 * p.2))

theorem s143_vdqC_mul (w : ℕ) : VdqCMulStatement w := by
  intro q1 q2 a1 a2 b1 b2 hsq hcop
  have hX0 : q1 * a1 * a2 ≠ 0 := (Nat.mul_ne_zero_iff.mp hsq.ne_zero).1
  have hY0 : q2 * b1 * b2 ≠ 0 := (Nat.mul_ne_zero_iff.mp hsq.ne_zero).2
  have hq1X : q1 ∣ q1 * a1 * a2 := Dvd.intro (a1 * a2) (by ring)
  have ha1X : a1 ∣ q1 * a1 * a2 := Dvd.intro (q1 * a2) (by ring)
  have ha2X : a2 ∣ q1 * a1 * a2 := Dvd.intro (q1 * a1) (by ring)
  have hq2Y : q2 ∣ q2 * b1 * b2 := Dvd.intro (b1 * b2) (by ring)
  have hb1Y : b1 ∣ q2 * b1 * b2 := Dvd.intro (q2 * b2) (by ring)
  have hb2Y : b2 ∣ q2 * b1 * b2 := Dvd.intro (q2 * b1) (by ring)
  have cop : ∀ x y : ℕ, x ∣ q1 * a1 * a2 → y ∣ q2 * b1 * b2 → Nat.Coprime x y :=
    fun x y hx hy => (hcop.coprime_dvd_left hx).coprime_dvd_right hy
  unfold vdqC
  rw [s143_sum_divisors_mul_coprime (cop _ _ ha1X hb1Y), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun e1 he1 => ?_)
  refine Finset.sum_congr rfl (fun f1 hf1 => ?_)
  rw [s143_sum_divisors_mul_coprime (cop _ _ ha2X hb2Y), Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun e2 he2 => ?_)
  refine Finset.sum_congr rfl (fun f2 hf2 => ?_)
  have de1 : e1 ∣ q1 * a1 * a2 := (Nat.dvd_of_mem_divisors he1).trans ha1X
  have de2 : e2 ∣ q1 * a1 * a2 := (Nat.dvd_of_mem_divisors he2).trans ha2X
  have df1 : f1 ∣ q2 * b1 * b2 := (Nat.dvd_of_mem_divisors hf1).trans hb1Y
  have df2 : f2 ∣ q2 * b1 * b2 := (Nat.dvd_of_mem_divisors hf2).trans hb2Y
  have dL1 : Nat.lcm e1 e2 ∣ q1 * a1 * a2 := Nat.lcm_dvd de1 de2
  have dL2 : Nat.lcm f1 f2 ∣ q2 * b1 * b2 := Nat.lcm_dvd df1 df2
  have dG1 : Nat.gcd e1 e2 ∣ q1 * a1 * a2 := (Nat.gcd_dvd_left _ _).trans de1
  have dG2 : Nat.gcd f1 f2 ∣ q2 * b1 * b2 := (Nat.gcd_dvd_left _ _).trans df1
  have hg : Nat.gcd (e1 * f1) (e2 * f2) = Nat.gcd e1 e2 * Nat.gcd f1 f2 := by
    rw [Nat.Coprime.gcd_mul _ (cop _ _ de2 df2),
      Nat.Coprime.gcd_mul_right_cancel _ ((cop _ _ de2 df1).symm),
      Nat.Coprime.gcd_mul_left_cancel _ (cop _ _ de1 df2)]
  have hG0 : Nat.gcd e1 e2 * Nat.gcd f1 f2 ≠ 0 :=
    Nat.mul_ne_zero (Nat.pos_of_dvd_of_pos dG1 (Nat.pos_of_ne_zero hX0)).ne'
      (Nat.pos_of_dvd_of_pos dG2 (Nat.pos_of_ne_zero hY0)).ne'
  have hl : Nat.lcm (e1 * f1) (e2 * f2) = Nat.lcm e1 e2 * Nat.lcm f1 f2 := by
    have h1 := Nat.gcd_mul_lcm (e1 * f1) (e2 * f2)
    have h2 := Nat.gcd_mul_lcm e1 e2
    have h3 := Nat.gcd_mul_lcm f1 f2
    rw [hg] at h1
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hG0)
    rw [h1]
    calc e1 * f1 * (e2 * f2) = (Nat.gcd e1 e2 * Nat.lcm e1 e2) * (Nat.gcd f1 f2 * Nat.lcm f1 f2) := by
          rw [h2, h3]; ring
      _ = _ := by ring
  have hdiv : (q1 * q2 ∣ Nat.lcm (e1 * f1) (e2 * f2)) ↔
      (q1 ∣ Nat.lcm e1 e2 ∧ q2 ∣ Nat.lcm f1 f2) := by
    rw [hl]
    constructor
    · intro h
      exact ⟨(cop _ _ hq1X dL2).dvd_of_dvd_mul_right ((Dvd.intro _ rfl).trans h),
        (cop _ _ dL1 hq2Y).symm.dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans h)⟩
    · rintro ⟨h1, h2⟩
      exact mul_dvd_mul h1 h2
  have hmu1 : (ArithmeticFunction.moebius (e1 * f1) : ℝ) =
      (ArithmeticFunction.moebius e1 : ℝ) * (ArithmeticFunction.moebius f1 : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (cop _ _ de1 df1)]
    push_cast; ring
  have hmu2 : (ArithmeticFunction.moebius (e2 * f2) : ℝ) =
      (ArithmeticFunction.moebius e2 : ℝ) * (ArithmeticFunction.moebius f2 : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (cop _ _ de2 df2)]
    push_cast; ring
  have hsum : ∑ t ∈ (Nat.gcd (e1 * f1) (e2 * f2)).divisors, 1 / envelopingH w t =
      (∑ t ∈ (Nat.gcd e1 e2).divisors, 1 / envelopingH w t) *
        ∑ t ∈ (Nat.gcd f1 f2).divisors, 1 / envelopingH w t := by
    rw [hg, s143_sum_divisors_mul_coprime (cop _ _ dG1 dG2), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => ?_))
    rw [vdq_H_mul_coprime w (cop _ _ ((Nat.dvd_of_mem_divisors hx).trans dG1)
      ((Nat.dvd_of_mem_divisors hy).trans dG2))]
    rw [one_div_mul_one_div]
  simp only [hdiv, hmu1, hmu2, hsum]
  by_cases hA : q1 ∣ Nat.lcm e1 e2 <;> by_cases hB : q2 ∣ Nat.lcm f1 f2 <;> simp [hA, hB]; ring

/-- Evaluation of the local coefficient at one prime, reference 18 formula 4.1.15, proved
in S143 round 2. The divisors of p are 1 and p; the eight cases are direct sums of at most four
terms. -/
theorem s143_vdqC_prime (w : ℕ) : VdqCPrimeStatement w := by
  intro p hp
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hH1 : envelopingH w 1 = 1 := by
    simp [envelopingH]
  have hmu : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  have hnd : ¬ p ∣ 1 := hp.not_dvd_one
  unfold vdqC
  simp only [hp.divisors, Nat.divisors_one, sum_insert (show (1:ℕ) ∉ ({p} : Finset ℕ) by
    simpa using h1p), sum_singleton, Nat.lcm_one_left, Nat.lcm_one_right, Nat.lcm_self,
    Nat.gcd_one_left, Nat.gcd_one_right, Nat.gcd_self, one_dvd, dvd_refl, ite_true, hnd,
    ite_false, hmu, ArithmeticFunction.moebius_apply_one, hH1]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, by norm_num, by norm_num, by norm_num, ?_⟩
  · ring
  · ring

/-- LEAF: induction over the prime factors of P of z, reference 18 formula 4.1.15, class HARD.
Given multiplicativity and the prime values, induct on the prime factors of lcm q m1 m2,
splitting off one prime at a time, and match the product of local factors with the closed
form, where H of m1 H of m2 times the local value gives h p, minus h p, or
minus h p squared times 1 minus 1 over h p. -/
theorem s143_local_coeff_induction {w : ℕ} (hw : 5 ≤ w) (hmul : VdqCMulStatement w)
    (hprime : VdqCPrimeStatement w) {z : ℝ} {q m1 m2 : ℕ}
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

/-- Assembly: the statement of `s143_local_coeff` from the three leaves above. -/
theorem s143_local_coeff_of_leaves :
    type_of% @LeanLab.Teravainen2016.s143_local_coeff := by
  intro w hw z q m1 m2 hq h1 h2
  exact s143_local_coeff_induction hw (s143_vdqC_mul w) (s143_vdqC_prime w) hq h1 h2

#print axioms s143_vdqC_mul
#print axioms s143_vdqC_prime
#print axioms s143_local_coeff_of_leaves

end LeanLab.Teravainen2016
