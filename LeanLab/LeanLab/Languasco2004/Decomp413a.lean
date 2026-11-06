/-
Perelli and Pintz 1993, page 44 displays 3 and 5, pages 46 to 48.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The cited comparison is PP1992 page 359 display 5.
Source http://www.numdam.org/item/CM_1992__82_3_355_0/.
AI wrote the Lean code. Goldbach is open.
The three smaller inputs stay OPEN. Existing declarations stay sealed.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.Decomp413a
open Finset Real MeasureTheory Decomp279b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 44 display 5: the minor part of the chosen integration period. -/
def minorDomain (N Y H B : ℝ) : Set ℝ := period H \ majorSet N Y B

/-- Page 44 display 5: S2 mass in a short interval centred at xi.
The period restriction gives the explicit endpoint version used here. -/
def localMass (N Y H B ξ : ℝ) : ℝ :=
  ∫ α in minorDomain N Y H B ∩ Set.Ioo (ξ - 1 / H) (ξ + 1 / H), ‖secondSum Y α‖ ^ 2

/-- Page 44 display 3: distance to the nearest integer, with the value H
at a kernel pole. This explicit value prevents inverse zero from losing a pole. -/
def kernel (H x : ℝ) : ℝ :=
  if x = (round x : ℤ) then H else min H (|x - (round x : ℤ)|⁻¹)

/-- Page 44 display 3: the squared kernel weighted S2 integral. -/
def kernelMass (N Y H B ξ : ℝ) : ℝ :=
  ∫ α in minorDomain N Y H B, ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2

/-- Page 44 display 3: the capped kernel is nonnegative for nonnegative H. -/
theorem kernel_nonneg {H : ℝ} (hH : 0 ≤ H) (x : ℝ) : 0 ≤ kernel H x := by
  unfold kernel
  split_ifs
  · exact hH
  · exact le_min hH (inv_nonneg.mpr (abs_nonneg _))

/-- Page 44 display 3: the cap also holds at the kernel poles. -/
theorem kernel_le (H x : ℝ) : kernel H x ≤ H := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Page 44 display 5: every local S2 mass is nonnegative. -/
theorem localMass_nonneg (N Y H B ξ : ℝ) : 0 ≤ localMass N Y H B ξ := by
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Page 44 display 3: every squared kernel mass is nonnegative. -/
theorem kernelMass_nonneg (N Y H B ξ : ℝ) : 0 ≤ kernelMass N Y H B ξ := by
  exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Pages 43 and 44: at Y = 1 the S2 sum vanishes since Lambda of one is zero.
This checks the domains of both new integrals without an analytic input. -/
theorem unit_length_instances (N H B ξ : ℝ) :
    localMass N 1 H B ξ = 0 ∧ kernelMass N 1 H B ξ = 0 := by
  have hsum : ∀ α : ℝ, secondSum 1 α = 0 := by
    intro α
    simp [secondSum]
  simp [localMass, kernelMass, hsum]

/-- Page 44 display 3: the value at an integer pole is the cap. -/
theorem kernel_pole_instance (H : ℝ) : kernel H 0 = H := by
  simp [kernel]

/-- LEAF. Page 44 display 5, proved on pages 46 to 48 through display 26.
Only the local S2 integral is estimated. The shifted period and real floors
are the endpoint version of the source's periodic and integer convention. -/
theorem local_mass_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ ξ : ℝ,
      localMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤
        C * localization N η / Real.log N ^ (2 * A + 3) := by sorry

/-- LEAF. Page 44 between displays 3 and 5, with the covering argument
also used in PP1992 page 359 display 5. Local mass in intervals of radius
1/H bounds the squared kernel integral by a constant times H squared.
This is a covering lemma. It has no zero density or coefficient estimate. -/
theorem kernel_from_local :
    ∃ D : ℝ, 0 < D ∧ ∀ N Y H B V : ℝ, 1 ≤ H → 0 ≤ V →
      (∀ ξ : ℝ, localMass N Y H B ξ ≤ V) →
      ∀ ξ : ℝ, kernelMass N Y H B ξ ≤ D * H ^ 2 * V := by sorry

/-- LEAF. Page 44 display 3, after Cauchy Schwarz, Parseval and
Brun Titchmarsh. Squaring removes the square root and supremum.
Only the Fourier coefficient to kernel comparison is asserted.
The constant is uniform in the chosen bound K for the kernel integral. -/
theorem coefficient_energy :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N → ∀ K : ℝ, 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤ K) →
      (∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) ^ 2 ≤
        D * (localization N η * Real.log N) ^ 3 * K := by sorry

/-- Page 44 displays 3 and 5 give the exact sealed minor_bound statement.
CONDITIONAL ON local_mass_bound, kernel_from_local and coefficient_energy. -/
theorem minor_bound_from_parts :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨e₁, he₁, hlocal⟩ := local_mass_bound
  obtain ⟨e₂, he₂, hcoeff⟩ := coefficient_energy
  obtain ⟨D, hD, hkernel⟩ := kernel_from_local
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro η A hη he hA
  obtain ⟨C, N₁, hC, hmass⟩ := hlocal η A hη (he.trans_le (min_le_left _ _)) hA
  obtain ⟨E, N₂, hE, henergy⟩ := hcoeff η A hη (he.trans_le (min_le_right _ _)) hA
  refine ⟨E * D * C + 1, max 3 (max N₁ N₂), ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hY : 0 < localization N η := Real.rpow_pos_of_pos hNp _
  have hH : 1 ≤ windowLength N η :=
    Real.one_le_rpow (by linarith) (by unfold lengthExponent; positivity)
  have hV : 0 ≤ C * localization N η / Real.log N ^ (2 * A + 3) := by positivity
  have hk := hkernel N (localization N η) (windowLength N η) (arcExponent η A)
    (C * localization N η / Real.log N ^ (2 * A + 3)) hH hV (hmass N hN1)
  have hK : 0 ≤ D * windowLength N η ^ 2 *
      (C * localization N η / Real.log N ^ (2 * A + 3)) := by positivity
  have hb := henergy N hN2 _ hK hk
  have hpow : Real.log N ^ (2 * A + 3) = (Real.log N ^ A) ^ 2 * Real.log N ^ (3 : ℕ) := by
    rw [Real.rpow_add hL, show 2 * A = A * 2 by ring, Real.rpow_mul hL.le]
    norm_num
  have hLp : Real.log N ^ A ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL A)
  have hrewrite : E * (localization N η * Real.log N) ^ 3 *
      (D * windowLength N η ^ 2 * (C * localization N η / Real.log N ^ (2 * A + 3))) =
      E * D * C * (windowLength N η * localization N η ^ 2 / Real.log N ^ A) ^ 2 := by
    rw [hpow]
    field_simp [hLp, hL.ne']
    <;> ring
  rw [hrewrite] at hb
  have hscale : 0 ≤ windowLength N η * localization N η ^ 2 / Real.log N ^ A := by positivity
  have hconstant : 0 ≤ E * D * C := by positivity
  have hsq : E * D * C ≤ (E * D * C + 1) ^ 2 := by nlinarith [sq_nonneg (E * D * C)]
  have hsum : 0 ≤ ∑ m ∈ window N η,
      ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbig := mul_le_mul_of_nonneg_right hsq (sq_nonneg
    (windowLength N η * localization N η ^ 2 / Real.log N ^ A))
  have hfinal : (∑ m ∈ window N η,
      ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) ≤
      (E * D * C + 1) * (windowLength N η * localization N η ^ 2 / Real.log N ^ A) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ E * D * C + 1) hscale]
  convert hfinal using 1 <;> ring

#print axioms kernel_nonneg
#print axioms kernel_le
#print axioms localMass_nonneg
#print axioms kernelMass_nonneg
#print axioms unit_length_instances
#print axioms kernel_pole_instance
#print axioms local_mass_bound
#print axioms kernel_from_local
#print axioms coefficient_energy
#print axioms minor_bound_from_parts
end
end LeanLab.Languasco2004.Decomp413a
