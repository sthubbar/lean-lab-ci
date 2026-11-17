import LeanLab.RamareSaouter2003.Decomp290c
import LeanLab.RamareSaouter2003.Decomp1531b

/-!
P0099 p. 19, the identity before display 13 and its main and logarithmic estimates.
This concrete instance checks that the actual zero contribution is nonzero.
Both affine scales remain in one integer cell, where psi is constant.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Vacuity594

open Real Chebyshev Smooth Thm4Assembly L3Zeta Decomp290c Set

/-- Derived nonvacuity instance for P0099 p. 19 before display 13.
At m equal to two, X equal to ten to the twelfth and u equal to ten to minus sixteen,
the actual total real zero contribution is strictly positive. -/
theorem zero_sum_positive_instance :
    0 < (∑' i : ZI, zeroTerm 2 (10 ^ 12) (1 / 10 ^ 16) i).re := by
  let X : ℝ := 10 ^ 12
  let u : ℝ := 1 / 10 ^ 16
  change 0 < (∑' i : ZI, zeroTerm 2 X u i).re
  have hu : 0 < u := by norm_num [u]
  have hX0 : 0 ≤ X := by norm_num [X]
  have he := Decomp1531a.exp_le_one_add_mul (m := 2) (by norm_num)
    (u := u) hu.le (by norm_num [u])
  simp only [Nat.cast_ofNat] at he
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have hcell (y : ℝ) (hy : X ≤ y) (hy1 : y < X + 1) : ψ y = ψ X := by
    rw [Chebyshev.psi_eq_psi_coe_floor y]
    have hfloor : ⌊y⌋₊ = 1000000000000 :=
      (Nat.floor_eq_iff (hX0.trans hy)).mpr
        (by
          norm_num [X] at hy hy1 ⊢
          exact ⟨hy, hy1⟩)
    rw [hfloor]
    congr 1
    norm_num [X]
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Dψ X u (2 * u) t = 0 := by
    have hlin0 : 0 ≤ 1 + 2 * u * t := by nlinarith [mul_nonneg hu.le ht.1]
    have hlin1 : 1 ≤ 1 + 2 * u * t := by nlinarith [mul_nonneg hu.le ht.1]
    have hlin2 : 1 + 2 * u * t ≤ 1 + 2 * u := by nlinarith [mul_nonneg hu.le (sub_nonneg.mpr ht.2)]
    have hp0 : 1 ≤ Real.exp u * (1 + 2 * u * t) :=
      one_le_mul_of_one_le_of_one_le he1 hlin1
    have hp1 : Real.exp u * (1 + 2 * u * t) ≤ (1 + 2 * u) ^ 2 := by
      have hh := mul_le_mul he hlin2 hlin0 (by positivity : 0 ≤ 1 + 2 * u)
      nlinarith only [hh]
    have htop0 : X ≤ X * Real.exp u * (1 + 2 * u * t) := by
      have hh := mul_le_mul_of_nonneg_left hp0 hX0
      nlinarith only [hh]
    have htop1 : X * Real.exp u * (1 + 2 * u * t) < X + 1 := by
      have hh := mul_le_mul_of_nonneg_left hp1 hX0
      have hgap : X * (1 + 2 * u) ^ 2 < X + 1 := by norm_num [X, u]
      nlinarith only [hh, hgap]
    have hbot0 : X ≤ X * (1 + 2 * u * t) := by nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hlin1)]
    have hbot1 : X * (1 + 2 * u * t) < X + 1 := by
      have hh := mul_le_mul_of_nonneg_left hlin2 hX0
      have hgap : X * (1 + 2 * u) < X + 1 := by norm_num [X, u]
      nlinarith only [hh, hgap]
    unfold Dψ
    rw [hcell _ htop0 htop1, hcell _ hbot0 hbot1, sub_self]
  have hJ : (∫ t in (0 : ℝ)..1, Dψ X u (2 * u) t * fm 2 t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        dsimp only
        rw [hD t ht, zero_mul]
      _ = 0 := by simp
  have hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ fm 2 t := by
    intro t ht
    unfold fm
    positivity
  have hmain := Decomp1531b.main_term_ge (continuous_fm 2).continuousOn hf0
    (u := u) (δ := 2 * u) (X := X) hu.le (by positivity) hX0
  have hlog := Decomp1531b.log_term_integral_le (continuous_fm 2).continuousOn hf0
    (X := X) (u := u) (δ := 2 * u) (by norm_num [X]) hu.le (by positivity)
  have hformula := weighted_formula_total 2 X u (by norm_num) (by norm_num [X])
    hu (by norm_num [u])
  simp only [Nat.cast_ofNat] at hformula
  rw [hJ] at hformula
  have hF := Decomp1531a.integral_fm_pos 2
  have hgap : 0 < (u * X - u / (2 * X)) * ∫ t in (0 : ℝ)..1, fm 2 t :=
    mul_pos (by norm_num [X, u]) hF
  have hbound := sub_le_sub hmain hlog
  rw [← sub_mul] at hbound
  have hpositive := lt_of_lt_of_le hgap hbound
  have hmain_eq := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hformula.symm)
  rw [hmain_eq, add_sub_cancel_left] at hpositive
  exact hpositive

/-- Derived nonvacuity instance for P0099 p. 19 before display 13.
At the same concrete parameters, an actual zero has a nonzero contribution.
The zero family and its analytic multiplicities are unchanged. -/
theorem exists_nonzero_zeroTerm_instance :
    ∃ i : ZI, zeroTerm 2 (10 ^ 12) (1 / 10 ^ 16) i ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hz : (∑' i : ZI, zeroTerm 2 (10 ^ 12) (1 / 10 ^ 16) i).re = 0 := by
    simp_rw [h]
    simp
  exact (ne_of_gt zero_sum_positive_instance) hz

end LeanLab.RamareSaouter2003.Vacuity594

#print axioms LeanLab.RamareSaouter2003.Vacuity594.zero_sum_positive_instance

#print axioms LeanLab.RamareSaouter2003.Vacuity594.exists_nonzero_zeroTerm_instance
