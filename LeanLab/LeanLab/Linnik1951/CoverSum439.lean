/-
P0093 page 166 equation 9.3. Finite cover summation with its exact edge case.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp376c

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 page 154 damped series definition, totalized endpoint N equal
to zero. The prime series has nonsummable unit norm terms and Lean assigns
its infinite sum value zero. This is separate from the positive N estimates. -/
theorem prime_fourier_zero439 (α : ℝ) : primeFourier111 0 α = 0 := by
  unfold primeFourier111
  apply tsum_eq_zero_of_not_summable
  intro hs
  have hn := hs.norm
  simp only [Nat.cast_zero, div_zero, Real.exp_zero, Complex.ofReal_one, one_mul,
    Complex.norm_exp_ofReal_mul_I] at hn
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp hn)

/-- P0093 page 166 equation 9.3. Exact cover_mass_summation357 type.
Subadditivity over the finite cover transfers the given per arc bounds
and factors out the common scale. No disjointness is required. -/
theorem cover_mass_summation_proved439 (N : ℕ) (η : ℝ) (F : Finset (ℕ × ℤ)) (B : ℝ)
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
  rcases Nat.eq_zero_or_pos N with rfl | hNpNat
  · norm_num [prime_fourier_zero439]
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpNat
  let τ := (N : ℝ) ^ (1 / 7 : ℝ)
  let f : ℝ → ℝ := fun α => ‖primeFourier111 N α‖ ^ 2
  let t : ℕ × ℤ → Set ℝ := fun p => Set.Icc
    ((p.2 : ℝ) / (p.1 : ℝ) - 1 / ((p.1 : ℝ) * τ))
    ((p.2 : ℝ) / (p.1 : ℝ) + 1 / ((p.1 : ℝ) * τ))
  have hf : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hi : ∀ p ∈ F, IntegrableOn f (t p) := by
    intro p hp
    exact ((continuous_prime_fourier111 N hN1).norm.pow 2).integrableOn_Icc
  have hUnion : (∫ x in ⋃ p ∈ F, t p, f x) ≤ ∑ p ∈ F, ∫ x in t p, f x := by
    clear hq harc hcover
    induction F using Finset.induction_on with
    | empty => simp
    | @insert p F hp ih =>
      have hip := hi p (Finset.mem_insert_self p F)
      have hiF : ∀ q ∈ F, IntegrableOn f (t q) :=
        fun q hq => hi q (Finset.mem_insert_of_mem hq)
      have hiU : IntegrableOn f (⋃ q ∈ F, t q) := integrableOn_finset_iUnion.mpr hiF
      have hle := integral_mono_measure
        (Measure.restrict_union_le (μ := volume) (t p) (⋃ q ∈ F, t q))
        (ae_of_all _ hf) (integrable_add_measure.mpr ⟨hip, hiU⟩)
      rw [integral_add_measure hip hiU] at hle
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Finset.sum_insert hp]
      exact hle.trans (add_le_add le_rfl (ih hiF))
  have hiU : IntegrableOn f (⋃ p ∈ F, t p) := integrableOn_finset_iUnion.mpr hi
  have hsum : (∫ x in exceptionalArcs280 N η, f x) ≤ ∑ p ∈ F, ∫ x in t p, f x :=
    (setIntegral_mono_set hiU (ae_of_all _ hf) (ae_of_all _ hcover)).trans hUnion
  have hτp : 0 < τ := Real.rpow_pos_of_pos hNp _
  have hpref : (N : ℝ) / τ = (N : ℝ) ^ (1 - (1 / 7 : ℝ)) := by
    rw [Real.rpow_sub hNp, Real.rpow_one]
  calc
    _ ≤ ∑ p ∈ F, ∫ x in t p, f x := hsum
    _ ≤ ∑ p ∈ F, B * (N : ℝ) / ((p.1 : ℝ) * τ) * Real.log N ^ 13 :=
      Finset.sum_le_sum harc
    _ = (B * ((N : ℝ) / τ) * Real.log N ^ 13) * (∑ p ∈ F, 1 / (p.1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hqp : (0 : ℝ) < p.1 := by exact_mod_cast (show 0 < p.1 by have := hq p hp; omega)
      field_simp
      <;> ring
    _ = _ := by rw [hpref]

end LeanLab.Linnik1951
