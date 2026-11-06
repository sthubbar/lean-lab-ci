import LeanLab.ExceptionalSet.PrimeTail385
import LeanLab.ExceptionalSet.Decomp404c

/-!
Supply for the finite scale tail on P0082 page 365 before display 24.
The real cutoff starts at 2. A factor 6 replaces the earlier factor 4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp428b

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.PrimeTail385

/-- LEAF. P0082 page 365 before display 24. Sum the unit interval decay
from the integer part of a real cutoff at least 2. -/
theorem outside_real_tail_two_le (P X Δ v T : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (hT : 2 ≤ T) :
    (∫ α in (Icc (-T) T)ᶜ, ‖integrand P X Δ v α‖) ≤
      6 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  let K : ℕ := ⌊T⌋₊
  have hK : 2 ≤ K := Nat.le_floor (by norm_num; linarith)
  have hfloor : (K : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
  have hcomp : T ≤ 3 * ((K : ℝ) - 1) := by
    have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hf : Integrable (fun α => ‖integrand P X Δ v α‖) :=
    (PrimeKernel264.total_integrable hΔ hΔ1 P X v).norm
  have hsub : (Icc (-T) T)ᶜ ⊆ (Icc (-(K : ℝ)) (K : ℝ))ᶜ := by
    intro x hx hmem
    exact hx ⟨(neg_le_neg hfloor).trans hmem.1, hmem.2.trans hfloor⟩
  have hmono : (∫ α in (Icc (-T) T)ᶜ, ‖integrand P X Δ v α‖) ≤
      (∫ α in (Icc (-(K : ℝ)) (K : ℝ))ᶜ, ‖integrand P X Δ v α‖) :=
    setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      hsub.eventuallySubset
  refine hmono.trans ((outside_nat_tail_le P X Δ v hX hΔ hΔ1 K hK).trans ?_)
  have hK1 : 0 < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hd1 : 0 < Δ * Real.pi ^ 2 * ((K : ℝ) - 1) := by positivity
  have hd2 : 0 < Δ * Real.pi ^ 2 * T := by positivity
  apply (div_le_div_iff₀ hd1 hd2).mpr
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hm := mul_le_mul_of_nonneg_left hcomp
    (show 0 ≤ 2 * (Real.log 4 * X * Real.log X) * (Δ * Real.pi ^ 2) by positivity)
  nlinarith only [hm]


/-- LEAF. P0082 page 365 display 24. Restrict any prime kernel integral
to the real interval at a cutoff at least 2. -/
theorem truncation_error_two_le (P X Δ v T : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hT : 2 ≤ T) (M : Set ℝ) :
    ‖(∫ α in M, integrand P X Δ v α) -
        (∫ α in M ∩ Icc (-T) T, integrand P X Δ v α)‖ ≤
      6 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T) := by
  have hf : Integrable (integrand P X Δ v) :=
    PrimeKernel264.total_integrable hΔ hΔ1 P X v
  have he := integral_inter_add_sdiff (t := Icc (-T) T) measurableSet_Icc
    (show IntegrableOn (integrand P X Δ v) M from hf.integrableOn)
  have hd : (∫ α in M, integrand P X Δ v α) -
      (∫ α in M ∩ Icc (-T) T, integrand P X Δ v α) =
      ∫ α in M \ Icc (-T) T, integrand P X Δ v α := by
    rw [← he]; abel
  rw [hd]
  refine (norm_integral_le_integral_norm _).trans (le_trans ?_
    (outside_real_tail_two_le P X Δ v T hX hΔ hΔ1 hT))
  exact setIntegral_mono_set hf.norm.integrableOn
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (show M \ Icc (-T) T ⊆ (Icc (-T) T)ᶜ from fun _ h => h.2).eventuallySubset

/-- Exact supply for Decomp404c.leaf_tail_integral. P0082 page 365 before
display 24. The explicit constant is 12 log 4 divided by pi squared.
The extra logarithm follows from log X at least one half for X at least 2. -/
theorem leaf_tail_integral_supplied : ∃ C : ℝ, 0 < C ∧
    ∀ P X Δ v : ℝ, 2 ≤ P → 2 ≤ X → 0 < Δ → Δ < 1 / 4 →
      ‖(∫ α in (majorArcs P X)ᶜ,
          Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v))) -
        (∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-P) P,
          Sp P X α ^ 2 * (Kfun Δ α : ℂ) * eC (-(α * v)))‖ ≤
            C * X * Real.log X ^ 2 / (Δ * P) := by
  refine ⟨12 * Real.log 4 / Real.pi ^ 2, by positivity, ?_⟩
  intro P X Δ v hP hX hΔ hΔ1
  have ht := truncation_error_two_le P X Δ v P hX hΔ (by linarith) hP
    (majorArcs P X)ᶜ
  have hL : (1 / 2 : ℝ) ≤ Real.log X := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX
    have := Real.log_two_gt_d9
    linarith
  have hlog : Real.log X ≤ 2 * Real.log X ^ 2 := by nlinarith
  change _ ≤ _ at ht
  exact ht.trans (by
    have hd : 0 < Δ * Real.pi ^ 2 * P := by positivity
    have he : (12 * Real.log 4 / Real.pi ^ 2) * X * Real.log X ^ 2 / (Δ * P) =
        6 * (Real.log 4 * X * (2 * Real.log X ^ 2)) / (Δ * Real.pi ^ 2 * P) := by
      field_simp
      <;> ring
    rw [he]
    gcongr)

end LeanLab.ExceptionalSet.Decomp428b
