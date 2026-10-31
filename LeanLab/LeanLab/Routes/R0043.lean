/-
R-0043, U-1387, PC 20261021T0703Z-4724, MOONSHOT T3. AI wrote this code.
Restriction route, Bourgain 1989 and Green 2005, applied to the binary Goldbach count.
Two blindness facts, neither is progress on Goldbach, which is OPEN.
1. `hoelder_floor`: for conjugate exponents p, q every Hölder pairing of a finite
   family bounds the L² mass from ABOVE, so no L^p restriction estimate, p ≠ 2,
   bounds the minor arc part of one Fourier coefficient below the L² bound.
2. `restriction_blind`: any downward closed property of finite sets, such as
   "dominated by the enveloping sieve majorant", which is the hypothesis class of
   every restriction estimate for the primes, holds for a subset of P with no
   representation of N.
-/
import Mathlib

open Finset

namespace LeanLab.Routes.R0043

/-- Log-convexity floor: Σ f² ≤ ‖f‖_p ‖f‖_q for conjugate p, q. -/
theorem hoelder_floor {ι : Type*} (s : Finset ι) (f : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i ^ 2 ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |f i| ^ q) ^ (1 / q) := by
  have h := Real.inner_le_Lp_mul_Lq s (fun i => |f i|) (fun i => |f i|) hpq
  simp only [abs_abs] at h
  calc ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, |f i| * |f i| := by
        refine sum_congr rfl fun i _ => ?_
        rw [← sq, sq_abs]
    _ ≤ _ := h

/-- One Fourier coefficient on a set of arcs is bounded by the L² mass there, and by
nothing smaller that depends only on |S|: the phase is the whole content. -/
theorem minor_coeff_le_l2 {ι : Type*} (m : Finset ι) (S e : ι → ℂ)
    (he : ∀ k ∈ m, ‖e k‖ = 1) :
    ‖∑ k ∈ m, S k ^ 2 * e k‖ ≤ ∑ k ∈ m, ‖S k‖ ^ 2 := by
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k hk => ?_))
  rw [norm_mul, norm_pow, he k hk, mul_one]

/-- The removal decoy for a target N: drop every a ≤ N with N ≤ 2a and N - a ∈ P. -/
def decoy (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  P.filter fun a => ¬ (a ≤ N ∧ N ≤ 2 * a ∧ N - a ∈ P)

theorem decoy_subset (P : Finset ℕ) (N : ℕ) : decoy P N ⊆ P := filter_subset _ _

theorem decoy_misses (P : Finset ℕ) (N : ℕ) :
    ∀ a ∈ decoy P N, ∀ b ∈ decoy P N, a + b ≠ N := by
  intro a ha b hb hab
  simp only [decoy, mem_filter] at ha hb
  rcases le_total b a with h | h
  · exact ha.2 ⟨by omega, by omega, by rw [show N - a = b by omega]; exact hb.1⟩
  · exact hb.2 ⟨by omega, by omega, by rw [show N - b = a by omega]; exact ha.1⟩

/-- Restriction blindness: a downward closed hypothesis class that contains P also
contains a subset of P that does not represent N. -/
theorem restriction_blind (Φ : Finset ℕ → Prop)
    (hdown : ∀ A B : Finset ℕ, B ⊆ A → Φ A → Φ B) (P : Finset ℕ) (hP : Φ P) (N : ℕ) :
    ∃ B ⊆ P, Φ B ∧ ∀ a ∈ B, ∀ b ∈ B, a + b ≠ N :=
  ⟨decoy P N, decoy_subset P N, hdown _ _ (decoy_subset P N) hP, decoy_misses P N⟩

/-- The majorant class of a restriction estimate: every element dominated by ν. -/
def Dominated (ν : ℕ → ℝ) (A : Finset ℕ) : Prop := ∀ n ∈ A, 1 ≤ ν n

theorem dominated_down (ν : ℕ → ℝ) :
    ∀ A B : Finset ℕ, B ⊆ A → Dominated ν A → Dominated ν B :=
  fun _ _ hBA hA n hn => hA n (hBA hn)

/-- Vacuity: the primes below 30 represent 28, the decoy keeps 8 of the 10 and loses 28. -/
example : (5 : ℕ) ∈ (range 30).filter Nat.Prime ∧ (23 : ℕ) ∈ (range 30).filter Nat.Prime ∧
    5 + 23 = 28 := by decide

example : (decoy ((range 30).filter Nat.Prime) 28).card = 8 := by decide

/-- Vacuity of `hoelder_floor`: p = q = 2 is a conjugate pair. -/
example : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two

end LeanLab.Routes.R0043

#print axioms LeanLab.Routes.R0043.hoelder_floor
#print axioms LeanLab.Routes.R0043.minor_coeff_le_l2
#print axioms LeanLab.Routes.R0043.decoy_misses
#print axioms LeanLab.Routes.R0043.restriction_blind
#print axioms LeanLab.Routes.R0043.dominated_down
