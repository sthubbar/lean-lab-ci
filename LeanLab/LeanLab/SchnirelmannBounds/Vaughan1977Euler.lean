/-
P0066, pages 95 and 105, elementary passage from the Euler products to finite moments.
Source: https://doi.org/10.1515/crll.1977.290.93
The numeric Euler product bounds remain cited inputs.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Moments

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Euler

open Vaughan1977Eq56 Vaughan1977Moments Vaughan1977Lemma3 Vaughan1977Lemma12

/-- A generic squarefree supported multiplicative divisor sum. -/
theorem divisor_product {g : ℕ → ℝ} (h1 : g 1 = 1)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → g (a * b) = g a * g b)
    (hsf : ∀ n, ¬ Squarefree n → g n = 0) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, g d = ∏ p ∈ n.primeFactors, (1 + g p) := by
  let af : ArithmeticFunction ℝ := ⟨g, hsf 0 not_squarefree_zero⟩
  have hmult : af.IsMultiplicative := ⟨h1, fun {_ _} h => hmul h⟩
  calc
    ∑ d ∈ n.divisors, g d = ∑ d ∈ n.divisors with Squarefree d, g d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hds
      exact hsf d (by simpa [hd] using hds)
    _ = ∑ s ∈ n.primeFactors.powerset, g (∏ p ∈ s, p) := by
      rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
      simp
    _ = ∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, g p := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hmult.map_prod_of_subset_primeFactors n s (Finset.mem_powerset.mp hs)
    _ = ∏ p ∈ n.primeFactors, (1 + g p) := by
      simpa [add_comm] using (Finset.prod_add (s := n.primeFactors) (f := g)
        (g := fun _ => (1 : ℝ))).symm

/-- A finite partial sum is bounded by the finite prime product up to the same cutoff. -/
theorem partial_sum_le_product {g : ℕ → ℝ} (h1 : g 1 = 1)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → g (a * b) = g a * g b)
    (hsf : ∀ n, ¬ Squarefree n → g n = 0) (h0 : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ d ∈ Icc 1 N, g d ≤ ∏ p ∈ N.primesLE, (1 + g p) := by
  let P := ∏ p ∈ N.primesLE, p
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesLE hp).ne_zero)
  have hPF : P.primeFactors = N.primesLE :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primesLE hp)
  have hsub : (Icc 1 N).filter Squarefree ⊆ P.divisors := by
    intro d hd
    obtain ⟨hdI, hds⟩ := Finset.mem_filter.mp hd
    have hdN := (Finset.mem_Icc.mp hdI).2
    have hfp : d.primeFactors ⊆ N.primesLE := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hdN,
        Nat.prime_of_mem_primeFactors hp⟩
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hP⟩
    rw [← Nat.prod_primeFactors_of_squarefree hds]
    exact Finset.prod_dvd_prod_of_subset _ _ id hfp
  calc
    ∑ d ∈ Icc 1 N, g d = ∑ d ∈ Icc 1 N with Squarefree d, g d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hds
      exact hsf d (by simpa [hd] using hds)
    _ ≤ ∑ d ∈ P.divisors, g d :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => h0 d)
    _ = ∏ p ∈ N.primesLE, (1 + g p) := by
      rw [divisor_product h1 hmul hsf hP, hPF]

theorem a_mul {m n : ℕ} (h : m.Coprime n) : a (m * n) = a m * a n := by
  simp only [a, f_mul h, Nat.totient_mul h, Nat.cast_mul]
  ring

theorem a_not_squarefree (n : ℕ) (hn : ¬ Squarefree n) : a n = 0 := by simp [a, f, hn]

theorem a_prime {p : ℕ} (hp : p.Prime) : a p = primeWeight p / ((p : ℝ) - 1) := by
  rw [a, f_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  norm_num

/-- The moment summand in 2.7. -/
def b (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 8 : ℝ) * a n

theorem b_one : b 1 = 1 := by norm_num [b, a_one]

theorem b_mul {m n : ℕ} (h : m.Coprime n) : b (m * n) = b m * b n := by
  rw [b, a_mul h, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  unfold b
  ring

theorem b_nonneg (n : ℕ) : 0 ≤ b n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (a_nonneg n)

theorem b_not_squarefree (n : ℕ) (hn : ¬ Squarefree n) : b n = 0 := by
  simp [b, a_not_squarefree n hn]

/-- Finite prime product form of the numeric upper bound in 2.6 and 2.11. -/
def EulerMassBound (C : ℝ) : Prop := ∀ N : ℕ,
  ∏ p ∈ N.primesLE, (1 + primeWeight p / ((p : ℝ) - 1)) ≤ C

/-- Finite prime product form of the upper bound in 2.7 and 2.12. -/
def EulerMomentBound : Prop := ∀ N : ℕ,
  ∏ p ∈ N.primesLE, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) ≤ 14.46

theorem mass_of_euler {C : ℝ} (h : EulerMassBound C) : MassBound C := by
  intro N
  have ht := partial_sum_le_product a_one (fun {_ _} => a_mul) a_not_squarefree a_nonneg N
  have he : (∏ p ∈ N.primesLE, (1 + a p)) =
      ∏ p ∈ N.primesLE, (1 + primeWeight p / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [a_prime (Nat.prime_of_mem_primesLE hp)]
  rw [he] at ht
  exact ht.trans (h N)

theorem moment_of_euler (h : EulerMomentBound) : MomentBound := by
  intro N
  have ht := partial_sum_le_product b_one (fun {_ _} => b_mul) b_not_squarefree b_nonneg N
  have he : (∏ p ∈ N.primesLE, (1 + b p)) =
      ∏ p ∈ N.primesLE, (1 + (p : ℝ) ^ (3 / 8 : ℝ) * primeWeight p / ((p : ℝ) - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [b, a_prime (Nat.prime_of_mem_primesLE hp)]
    ring
  rw [he] at ht
  exact ht.trans (h N)

/-- Equation 5.10 with only the cited theta, Brun Titchmarsh and numeric product inputs. -/
theorem eq510tail_of_euler {C : ℝ} (hC : C ≤ 6.2130) (hBT : Lemma3Coprime)
    (hTheta : ThetaUpper) (hMass : EulerMassBound C) (hMoment : EulerMomentBound) :
    Vaughan1977Eq55.Eq510tail C :=
  eq510tail_of_moments hC hBT hTheta (mass_of_euler hMass) (moment_of_euler hMoment)

/-- The 27 prime route after the elementary mass and moment inputs are discharged. -/
theorem statement27_of_euler {C : ℝ} (hClow : 6.2022 ≤ C) (hCup : C ≤ 6.2130)
    (hRS : LeanLab.RieselVaughan1983.RS33)
    (h8 : Vaughan1977Lemma10.Lemma8 LeanLab.ChenExplicit.twinC) (h11 : Lemma11)
    (hBT : Lemma3Coprime) (hTheta : ThetaUpper)
    (hMass : EulerMassBound C) (hMoment : EulerMomentBound) : Vaughan1977.Statement27 :=
  statement27_of_moments hClow hCup hRS h8 h11 hBT hTheta
    (mass_of_euler hMass) (moment_of_euler hMoment)

example : (∑ d ∈ Icc 1 (1 : ℕ), a d) = 1 := by simp [a_one]

example : (∏ p ∈ (2 : ℕ).primesLE, (1 + primeWeight p / ((p : ℝ) - 1))) = 1 := by
  have hp : (2 : ℕ).primesLE = {2} := by decide
  rw [hp, Finset.prod_singleton]
  norm_num [primeWeight]

end LeanLab.SchnirelmannBounds.Vaughan1977Euler

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.divisor_product
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.partial_sum_le_product
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.a_mul
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.a_not_squarefree
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.a_prime
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.b_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.b_mul
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.b_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.b_not_squarefree
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.mass_of_euler
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.moment_of_euler
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.eq510tail_of_euler
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Euler.statement27_of_euler
