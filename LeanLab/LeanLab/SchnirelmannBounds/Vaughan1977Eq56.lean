/-
Vaughan 1977, P0066, page 104, the multiplicative function preceding equation 5.6.
Source: https://doi.org/10.1515/crll.1977.290.93
AI wrote this Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset Real Nat
open scoped Classical

noncomputable section
namespace LeanLab.SchnirelmannBounds.Vaughan1977Eq56

/-- The prime value of the function on page 104. The even prime has value zero. -/
def primeWeight (p : ℕ) : ℝ :=
  if p = 2 then 0 else (((p : ℝ) - 1) / ((p : ℝ) - 2)) ^ (11 / 4 : ℝ) - 1

/-- The function preceding 5.6, supported on squarefree odd integers. -/
def f (n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, primeWeight p else 0

theorem f_one : f 1 = 1 := by simp [f]

theorem f_prime {p : ℕ} (hp : p.Prime) : f p = primeWeight p := by
  simp [f, hp.squarefree, hp.primeFactors]

theorem f_even {n : ℕ} (hn : 2 ∣ n) : f n = 0 := by
  unfold f
  split_ifs with hs
  · apply Finset.prod_eq_zero (Nat.prime_two.mem_primeFactors hn hs.ne_zero)
    simp [primeWeight]
  · rfl

theorem f_prime_pow {p m : ℕ} (hp : p.Prime) (hm : 1 < m) : f (p ^ m) = 0 := by
  have hs : ¬ Squarefree (p ^ m) := by
    rw [squarefree_pow_iff hp.ne_one (by omega)]
    simp only [not_and_or]
    exact Or.inr (by omega)
  simp [f, hs]

theorem f_mul {a b : ℕ} (hab : a.Coprime b) : f (a * b) = f a * f b := by
  by_cases ha : Squarefree a
  · by_cases hb : Squarefree b
    · rw [f, ite_eq_left ((squarefree_mul hab).mpr ⟨ha, hb⟩),
        Nat.primeFactors_mul ha.ne_zero hb.ne_zero,
        Finset.prod_union hab.disjoint_primeFactors, f, ite_eq_left ha, f, ite_eq_left hb]
    · have hn : ¬ Squarefree (a * b) := fun h => hb ((squarefree_mul hab).mp h).2
      simp [f, hb, hn]
  · have hn : ¬ Squarefree (a * b) := fun h => ha ((squarefree_mul hab).mp h).1
    simp [f, ha, hn]

theorem f_nonneg (n : ℕ) : 0 ≤ f n := by
  unfold f
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    unfold primeWeight
    split_ifs with h
    · norm_num
    · have hp3 : (2 : ℝ) < p := by exact_mod_cast (show 2 < p by omega)
      have hq : (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have hr := Real.one_le_rpow hq (by norm_num : (0 : ℝ) ≤ 11 / 4)
      simpa using sub_nonneg.mpr hr
  · exact le_rfl

/-- Divisor expansion of the weight, before the finite sums in 5.6 are exchanged. -/
theorem sum_divisors_f {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, f d = ∏ p ∈ n.primeFactors, (1 + primeWeight p) := by
  calc
    ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors with Squarefree d, f d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hds
      have hs : ¬ Squarefree d := by simpa [hd] using hds
      simp [f, hs]
    _ = ∑ s ∈ n.primeFactors.powerset, f (∏ p ∈ s, p) := by
      rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
      simp
    _ = ∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, primeWeight p := by
      apply Finset.sum_congr rfl
      intro s hs
      have hp : ∀ p ∈ s, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp)
      have hsq : Squarefree (∏ p ∈ s, p) := by
        apply Finset.squarefree_prod_of_pairwise_isCoprime
        · intro p hps q hqs hpq
          exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hps) (hp q hqs)).mpr hpq)
        · intro p hps
          exact (hp p hps).squarefree
      rw [f, ite_eq_left hsq, Nat.primeFactors_prod hp]
    _ = ∏ p ∈ n.primeFactors, (1 + primeWeight p) := by
      simpa [add_comm] using (Finset.prod_add (s := n.primeFactors) (f := primeWeight)
        (g := fun _ => (1 : ℝ))).symm

/-- A concrete instance of the local prime rule and of the divisor expansion. -/
example : f 1 = 1 ∧ f 2 = 0 ∧ f 9 = 0 ∧ f 3 = (2 : ℝ) ^ (11 / 4 : ℝ) - 1 := by
  refine ⟨f_one, f_even (dvd_refl 2), ?_, ?_⟩
  · exact f_prime_pow Nat.prime_three (m := 2) (by norm_num)
  · rw [f_prime Nat.prime_three]
    norm_num [primeWeight]

end LeanLab.SchnirelmannBounds.Vaughan1977Eq56

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_prime
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_even
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_prime_pow
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_mul
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.f_nonneg
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Eq56.sum_divisors_f
