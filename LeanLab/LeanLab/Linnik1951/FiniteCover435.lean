/-
P0093 page 166. Finite cover summation for the fresh main input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_exceptional_prime_mass357
import LeanLab.Linnik1951.Decomp376c

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 166 proof of equation 9.3. The already proved finite
cover integral argument works for any finite index type. It bounds a
nonnegative integral by the sum of the covering integrals. -/
theorem finite_cover_integral_indexed435 {ι : Type*} (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (S : Finset ι) (t : ι → Set ℝ)
    (hi : ∀ q ∈ S, IntegrableOn f (t q))
    (hcover : s ⊆ ⋃ q ∈ S, t q) :
    (∫ x in s, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
  classical
  have hUnion : (∫ x in ⋃ q ∈ S, t q, f x) ≤ ∑ q ∈ S, ∫ x in t q, f x := by
    clear hcover
    induction S using Finset.induction_on with
    | empty => simp
    | @insert q S hq ih =>
      have hiq := hi q (Finset.mem_insert_self q S)
      have hiS : ∀ i ∈ S, IntegrableOn f (t i) := fun i hi' => hi i (Finset.mem_insert_of_mem hi')
      have hiU : IntegrableOn f (⋃ i ∈ S, t i) := integrableOn_finset_iUnion.mpr hiS
      have hle := integral_mono_measure (Measure.restrict_union_le (μ := volume) (t q) (⋃ i ∈ S, t i))
        (ae_of_all _ hf) (integrable_add_measure.mpr ⟨hiq, hiU⟩)
      rw [integral_add_measure hiq hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert hq]
      exact hle.trans (add_le_add le_rfl (ih hiS))
  have hiU : IntegrableOn f (⋃ q ∈ S, t q) := integrableOn_finset_iUnion.mpr hi
  exact (setIntegral_mono_set hiU (ae_of_all _ hf) (ae_of_all _ hcover)).trans hUnion


/-- P0093 page 154 definition of S. At the unused parameter N zero,
the totalized Lean series has value zero because every term has norm
one on the infinite prime index type and the series is not summable.
This handles the zero case in the fresh unrestricted cover statement. -/
theorem prime_fourier_zero_parameter435 (α : ℝ) : primeFourier111 0 α = 0 := by
  unfold primeFourier111
  apply tsum_eq_zero_of_not_summable
  intro hs
  have hn := hs.norm
  have hn' : Summable (fun _p : Nat.Primes => (1 : ℝ)) := by
    simpa only [norm_mul, Nat.cast_zero, div_zero, Real.exp_zero, Complex.ofReal_one,
      norm_one, one_mul, mul_one,
      Complex.norm_exp_ofReal_mul_I] using hn
  have hbad : (1 : ℝ) = 0 := (summable_const_iff (1 : ℝ)).mp hn' 
  norm_num at hbad

/-- P0093 page 166 proof of equation 9.3. Exact
cover_mass_summation357 statement from finite integral subadditivity.
The per arc numerical estimates are explicit hypotheses. -/
theorem cover_mass_summation_proved435 (N : ℕ) (η : ℝ) (F : Finset (ℕ × ℤ)) (B : ℝ)
    (hB : 0 ≤ B)
    (hq : ∀ p ∈ F, 1 ≤ p.1)
    (hcover : exceptionalArcs280 N η ⊆
      ⋃ p ∈ F, Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
        ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))))
    (harc : ∀ p ∈ F,
      (∫ α in Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
          ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
        ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13) :
    (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
      B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 13 *
        (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [prime_fourier_zero_parameter435]
  have h1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let t : ℕ × ℤ → Set ℝ := fun p =>
    Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
      ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
  have hi : ∀ p ∈ F, IntegrableOn (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) (t p) := by
    intro p hp
    exact ((continuous_prime_fourier111 N h1).norm.pow 2).integrableOn_Icc
  have hb := finite_cover_integral_indexed435 (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2)
    (fun α => sq_nonneg _) (exceptionalArcs280 N η) F t hi hcover
  have hscale : (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (1 - (1 / 7 : ℝ)) := by
    rw [Real.rpow_sub hNp, Real.rpow_one]
  calc
    _ ≤ ∑ p ∈ F, ∫ α in t p, ‖primeFourier111 N α‖ ^ 2 := hb
    _ ≤ ∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 :=
      Finset.sum_le_sum harc
    _ = ∑ p ∈ F, (B * (N : ℝ) ^ (1 - (1 / 7 : ℝ)) * Real.log N ^ 13) *
        (1 / (p.1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← hscale]
      ring
    _ = _ := (Finset.mul_sum F _ _).symm

end LeanLab.Linnik1951
