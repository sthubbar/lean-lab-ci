/-
AI wrote this Lean code for CODEX task51.
P0074 page 11, the low-modulus residue assembly in Lemma 4.1.
The residue distribution and nonunit mass bounds remain explicit inputs.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.GaussBounds

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- A coprime shift of the principal Gauss sum still equals the Möbius value. -/
theorem principal_shift_gauss_eq {q : ℕ} [NeZero q] (r : ZMod q) (hr : IsUnit r) :
    gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift r) =
      (ArithmeticFunction.moebius q : ℂ) := by
  have h := gaussSum_mulShift_eq (1 : DirichletCharacter ℂ q) ZMod.stdAddChar hr.unit
  simpa only [hr.unit_spec, inv_one, MulChar.one_apply hr, one_mul, gaussSum_principal] using h

/-- Uniform residue errors and bounded total nonunit mass give the low-modulus Fourier main term. -/
theorem residue_fourier_approx {q : ℕ} [NeZero q] (r : ZMod q) (hr : IsUnit r)
    (mass : ZMod q → ℝ) (M E B : ℝ)
    (hunit : ∀ a : ZMod q, IsUnit a → |mass a - M / q.totient| ≤ E)
    (hnon : ∑ a : ZMod q, (if IsUnit a then (0 : ℝ) else |mass a|) ≤ B) :
    ‖(∑ a : ZMod q, (mass a : ℂ) * ZMod.stdAddChar (r * a)) -
        (ArithmeticFunction.moebius q : ℂ) * M / q.totient‖ ≤ (q.totient : ℝ) * E + B := by
  have hmain : (∑ a : ZMod q,
      (if IsUnit a then ((M / q.totient : ℝ) : ℂ) else 0) * ZMod.stdAddChar (r * a)) =
      (ArithmeticFunction.moebius q : ℂ) * M / q.totient := by
    calc
      _ = ((M / q.totient : ℝ) : ℂ) *
          gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift r) := by
        rw [gaussSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [AddChar.mulShift_apply]
        by_cases hu : IsUnit a
        · rw [ite_eq_left hu, MulChar.one_apply hu]
          ring
        · rw [ite_eq_right hu, MulChar.map_nonunit _ hu]
          simp
      _ = _ := by
        rw [principal_shift_gauss_eq r hr]
        push_cast
        ring
  have heq : (∑ a : ZMod q, (mass a : ℂ) * ZMod.stdAddChar (r * a)) -
      (ArithmeticFunction.moebius q : ℂ) * M / q.totient =
      ∑ a : ZMod q,
        (((mass a - if IsUnit a then M / q.totient else 0 : ℝ) : ℂ)) *
          ZMod.stdAddChar (r * a) := by
    simp_rw [Complex.ofReal_sub, sub_mul]
    rw [Finset.sum_sub_distrib, ← hmain]
    congr 2
    funext a
    split_ifs <;> simp
  have hcount : (∑ a : ZMod q, if IsUnit a then E else 0) = (q.totient : ℝ) * E := by
    have h := sum_isUnit_eq_totient (q := q)
    calc
      _ = (∑ a : ZMod q, if IsUnit a then (1 : ℝ) else 0) * E := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        split_ifs <;> simp
      _ = _ := by rw [h]
  rw [heq]
  calc
    _ ≤ ∑ a : ZMod q,
        ‖(((mass a - if IsUnit a then M / q.totient else 0 : ℝ) : ℂ)) *
          ZMod.stdAddChar (r * a)‖ := norm_sum_le _ _
    _ ≤ ∑ a : ZMod q, ((if IsUnit a then E else 0) +
        (if IsUnit a then 0 else |mass a|)) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul, norm_stdAddChar, mul_one, Complex.norm_real, Real.norm_eq_abs]
      by_cases hu : IsUnit a
      · simpa only [ite_eq_left hu, add_zero] using hunit a hu
      · simp only [ite_eq_right hu, sub_zero, zero_add, le_refl]
    _ = (q.totient : ℝ) * E +
        ∑ a : ZMod q, (if IsUnit a then (0 : ℝ) else |mass a|) := by
      rw [Finset.sum_add_distrib, hcount]
    _ ≤ _ := add_le_add le_rfl hnon

#print axioms principal_shift_gauss_eq
#print axioms residue_fourier_approx
end LeanLab.Grimmelt2019.MainTerm
