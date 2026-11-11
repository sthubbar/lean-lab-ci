import LeanLab.ExceptionalSet.OddCoefficient467
import LeanLab.ExceptionalSet.OddTail467

/-!
P0082 page368 displays32 to35.
The boundary and truncation transfers reuse the existing shifted kernel supplies.
The remaining phase estimate is not assumed proved.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483a

open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.U1539 (Sp R1 eC majorArcs hcheck)
open LeanLab.ExceptionalSet.OddCoefficient467 (minorCoefficient)

/-- P0082 page368 before display33. Each minor coefficient is bounded by
one period of the prime square mass, with Mathlib's explicit Chebyshev constant. -/
theorem minorCoefficient_norm_le (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖minorCoefficient P X m‖ ≤ Real.log 4 * X * Real.log X := by
  classical
  unfold minorCoefficient hcheck
  refine (intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun α _ => ?_))
    (show IntervalIntegrable (fun α => ‖Sp P X α‖ ^ 2) volume 0 1 from
      (by unfold Sp eC; fun_prop : Continuous (fun α : ℝ => ‖Sp P X α‖ ^ 2)).intervalIntegrable _ _)).trans ?_
  · by_cases ha : α ∈ majorArcs P X
    · simp [ha]
    · simp [ha, norm_pow, U1539.norm_eC]
  · simpa only [zero_add] using PrimeEnergy385.prime_energy_le P X 0 hX

/-- P0082 page368 displays32 and33. For an arbitrary finite index set
whose upper adjacent integer is odd, the major coefficient moment is bounded
by the full shifted minor moment and the explicit fractional boundary mass. -/
theorem odd_upper_moment_transfer (P X Δ : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd (⌊v n⌋ + 1)) :
    (∑ n ∈ s, ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  classical
  let bad := fun n => Int.fract (v n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (v n)
  let f := fun n => ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2
  let g := fun n => ‖∫ α in (majorArcs P X)ᶜ,
    OddTail467.integrand P X Δ (v n) α‖ ^ 2
  have hb (n : ℕ) (hn : n ∈ s) : f n ≤ (Real.log 4 * X * Real.log X) ^ 2 := by
    have h := minorCoefficient_norm_le P X hX (⌊v n⌋ + 1)
    rw [OddCoefficient467.odd_minor_eq_neg_major P X hP _ (hodd n hn), norm_neg] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hg (n : ℕ) (hn : n ∈ s) (hgood : ¬ bad n) : f n = g n := by
    have hl : Δ / 2 ≤ Int.fract (v n) := le_of_not_gt (fun h => hgood (Or.inl h))
    have hr : Int.fract (v n) ≤ 1 - Δ / 2 := le_of_not_gt (fun h => hgood (Or.inr h))
    have hi := OddCoefficient467.plateau_odd_major_identity P X Δ (v n)
      hP hΔ hΔ1 (hodd n hn) hl hr
    dsimp only [f, g, OddTail467.integrand]
    rw [hi, norm_neg]
  change (∑ n ∈ s, f n) ≤ (∑ n ∈ s, g n) + _
  rw [← sum_filter_add_sum_filter_not s bad f]
  have hbad : ∑ n ∈ s.filter bad, f n ≤
      ((s.filter bad).card : ℝ) * (Real.log 4 * X * Real.log X) ^ 2 := by
    calc _ ≤ ∑ n ∈ s.filter bad, (Real.log 4 * X * Real.log X) ^ 2 :=
        sum_le_sum (fun n hn => hb n (mem_filter.mp hn).1)
      _ = _ := by simp
  have hgood : ∑ n ∈ s.filter (fun n => ¬ bad n), f n ≤ ∑ n ∈ s, g n := by
    calc _ = ∑ n ∈ s.filter (fun n => ¬ bad n), g n :=
        sum_congr rfl (fun n hn => hg n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun n _ _ => sq_nonneg _)
  exact (add_le_add hbad hgood).trans_eq (by dsimp [bad]; ring)


/-- P0082 page368 tail removal before display35. The existing absolute tail
bound controls the second moment on every finite index set. -/
theorem shifted_truncation_moment (P X Δ T : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
      OddTail467.integrand P X Δ (v n) α‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
  let τ := 8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)
  have hp (n : ℕ) :
      ‖∫ α in (majorArcs P X)ᶜ, OddTail467.integrand P X Δ (v n) α‖ ^ 2 ≤
        2 * ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
          OddTail467.integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2 := by
    let a := ∫ α in (majorArcs P X)ᶜ, OddTail467.integrand P X Δ (v n) α
    let b := ∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
      OddTail467.integrand P X Δ (v n) α
    have ht : ‖a - b‖ ≤ τ := OddTail467.truncation_error_le P X Δ (v n) T
      hX hΔ hΔ1 hT _
    have hnorm : ‖a‖ ≤ ‖b‖ + τ := by
      calc ‖a‖ = ‖b + (a - b)‖ := by congr 1; abel
        _ ≤ ‖b‖ + ‖a - b‖ := norm_add_le _ _
        _ ≤ ‖b‖ + τ := by linarith [ht]
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (add_sq_le.trans_eq (by ring))
  calc _ ≤ ∑ n ∈ s,
      (2 * ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2 + 2 * τ ^ 2) :=
      sum_le_sum (fun n _ => hp n)
    _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp [τ]; ring

/-- P0082 page367 display30 and the indicated cognate kernel argument.
Subtracting one from the phase frequency extracts the lower adjacent odd coefficient. -/
theorem odd_lower_moment_transfer (P X Δ : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd ⌊v n⌋) :
    (∑ n ∈ s, ‖R1 P X ⌊v n⌋‖ ^ 2) ≤
      (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ,
        OddTail467.integrand P X Δ (v n - 1) α‖ ^ 2) +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  simpa only [Int.floor_sub_one, sub_add_cancel, Int.fract_sub_one] using
    odd_upper_moment_transfer P X Δ hP hX hΔ hΔ1 s (fun n => v n - 1)
      (fun n hn => by simpa only [Int.floor_sub_one, sub_add_cancel] using hodd n hn)


/-- P0082 page368 display35. The upper adjacent moment reduces to the
truncated shifted moment, an explicit tail mass and a fractional boundary mass. -/
theorem odd_upper_truncated_moment (P X Δ T : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd (⌊v n⌋ + 1)) :
    (∑ n ∈ s, ‖R1 P X (⌊v n⌋ + 1)‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  have hu := odd_upper_moment_transfer P X Δ hP hX hΔ hΔ1 s v hodd
  have ht := shifted_truncation_moment P X Δ T hX hΔ hΔ1 hT s v
  linarith only [hu, ht]


/-- P0082 page367 display30 and page368 display35, the lower adjacent case.
Only the phase frequency changes in the same boundary and tail transfer. -/
theorem odd_lower_truncated_moment (P X Δ T : ℝ) (hP : 2 ≤ P) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 4 ≤ T) (s : Finset ℕ) (v : ℕ → ℝ)
    (hodd : ∀ n ∈ s, Odd ⌊v n⌋) :
    (∑ n ∈ s, ‖R1 P X ⌊v n⌋‖ ^ 2) ≤
      2 * (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
        OddTail467.integrand P X Δ (v n - 1) α‖ ^ 2) +
      2 * (s.card : ℝ) *
        (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 +
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) *
          (Real.log 4 * X * Real.log X) ^ 2) := by
  simpa only [Int.floor_sub_one, sub_add_cancel, Int.fract_sub_one] using
    odd_upper_truncated_moment P X Δ T hP hX hΔ hΔ1 hT s (fun n => v n - 1)
      (fun n hn => by simpa only [Int.floor_sub_one, sub_add_cancel] using hodd n hn)

end LeanLab.ExceptionalSet.Decomp483a
