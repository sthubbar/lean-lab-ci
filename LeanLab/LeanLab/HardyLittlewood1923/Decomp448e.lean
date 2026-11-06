import LeanLab.HardyLittlewood1923.Prime448
import LeanLab.HardyLittlewood1923.Decomp415c
import LeanLab.PNTPort.Vinogradov.MajorArc
import LeanLab.PNTPort.Vinogradov.MinorArcs

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 7 to 10 equations 2.11 to 2.21.
The page 69 correction to imprimitive Gauss sums remains in force.
Goldbach is OPEN.
-/
namespace LeanLab.HardyLittlewood1923.Decomp448e
open Real Finset ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp415c

/-- LEAF. P0004 pages 9 and 10 Lemma 2 equation 2.21.
The prime series differs from the unit restricted von Mangoldt series by the f1 remainder.
Its mass is bounded before any character estimate or zero free hypothesis is used. -/
theorem prime_unit_correction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], ∀ p : ℕ, ∀ θ : ℝ,
        ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) -
          Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ)‖ ≤
            C * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ A := by
  exact Prime448.prime_unit_correction

/-- P0004 page 8 equation 2.15. The principal Gauss sum is the coprime Ramanujan sum. -/
theorem principal_gauss_sum {q : ℕ} [NeZero q] {p : ℕ}
    (hq : 1 ≤ q) (hpq : p.Coprime q) :
    gaussSum (1 : DirichletCharacter ℂ q) (stdAddChar.mulShift (p : ZMod q)) =
      (μ q : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q)
      (stdAddChar.mulShift (p : ZMod q)) =
      ∑ r ∈ range q, (1 : DirichletCharacter ℂ q) (r : ZMod q) *
        (stdAddChar.mulShift (p : ZMod q)) (r : ZMod q) := by
    simpa only [gaussSum, ZMod.natCast_zmod_val] using
      LeanLab.PNTPort.Vinogradov.sum_zmod_eq_range (M := q)
        (fun r : ℕ => (1 : DirichletCharacter ℂ q) (r : ZMod q) *
          (stdAddChar.mulShift (p : ZMod q)) (r : ZMod q))
  rw [hsum]
  have he (r : ℕ) :
      (1 : DirichletCharacter ℂ q) (r : ZMod q) *
        (stdAddChar.mulShift (p : ZMod q)) (r : ZMod q) =
      if r.Coprime q then LeanLab.PNTPort.LargeSieve.e ((p : ℝ) * r / q) else 0 := by
    by_cases hr : r.Coprime q
    · have hu : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hr
      rw [MulChar.one_apply hu]
      simp only [one_mul, if_pos hr, AddChar.mulShift_apply]
      rw [show (p : ZMod q) * (r : ZMod q) = ((p * r : ℕ) : ZMod q) by simp,
        ← Int.cast_natCast (p * r), stdAddChar_coe]
      unfold LeanLab.PNTPort.LargeSieve.e
      push_cast
      congr 1
      ring
    · have hu : ¬ IsUnit (r : ZMod q) := by simpa only [ZMod.isUnit_iff_coprime] using hr
      simp [MulChar.map_nonunit _ hu, hr]
  simp_rw [he]
  rw [← sum_filter]
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := by exact_mod_cast hpq.isCoprime
  simpa using LeanLab.PNTPort.Vinogradov.ramanujan_coprime hq hcop

/-- P0004 pages 7 and 8 equations 2.11 to 2.16.
The proved character expansion isolates the exact principal pole. -/
theorem centered_character_expansion {n q : ℕ} [NeZero q]
    (hn : 0 < n) {p : ℕ} (hq : 1 ≤ q) (hpq : p.Coprime q) (θ : ℝ) :
    Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ) - localPhi n q θ =
      ∑ χ : DirichletCharacter ℂ q,
        (gaussSum χ (stdAddChar.mulShift (p : ZMod q)) / (q.totient : ℂ)) *
          characterError n q χ⁻¹ θ := by
  classical
  have hz : 0 < (localY n θ).re := by rw [localY_re]; positivity
  rw [Task52.weighted_character_expansion _ hz]
  simp_rw [characterError, mul_sub]
  rw [sum_sub_distrib]
  congr 1
  simp only [inv_eq_one, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [principal_gauss_sum hq hpq]
  simp only [localPhi, div_eq_mul_inv]

/-- P0004 page 19 equation 2.811 and the page 21 averaging step.
The exact sealed reduction follows from the f1 mass and the proved character expansion.
The prime unit correction is independently proved. -/
theorem prime_character_reduction :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (q : ℕ) [NeZero q], 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          (Real.sqrt q / (q.totient : ℝ)) *
            (∑ χ : DirichletCharacter ℂ q, ‖characterError n q χ θ‖) +
          C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) * Real.log ((q : ℝ) + 1) ^ A := by
  classical
  obtain ⟨A, C, hC, hc⟩ := prime_unit_correction
  refine ⟨A, C, hC, fun n hn q _ hq _ p _ hpq θ _ => ?_⟩
  have hnpos : 0 < n := by omega
  have hid := centered_character_expansion hnpos hq hpq θ
  have hbound : ‖Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ) -
      localPhi n q θ‖ ≤ (Real.sqrt q / (q.totient : ℝ)) *
        (∑ χ : DirichletCharacter ℂ q, ‖characterError n q χ θ‖) := by
    rw [hid]
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖(gaussSum χ (stdAddChar.mulShift (p : ZMod q)) / (q.totient : ℂ)) *
            characterError n q χ⁻¹ θ‖ := norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          (Real.sqrt q / (q.totient : ℝ)) * ‖characterError n q χ⁻¹ θ‖ := by
        apply sum_le_sum
        intro χ _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [ZMod.coe_unitOfCoprime] using
          Task52.shifted_gauss_coefficient_bound χ (ZMod.unitOfCoprime p hpq)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q))
          (fun χ : DirichletCharacter ℂ q => ‖characterError n q χ θ‖)
  have hsqrt : 1 ≤ Real.sqrt (q : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ q by exact_mod_cast hq)
  have hlog : 0 ≤ Real.log ((q : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hr := hc n hn q p θ
  have htriangle : ‖localError n p q θ‖ ≤
      ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) -
        Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ)‖ +
      ‖Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ) - localPhi n q θ‖ := by
    simpa only [sub_add_sub_cancel, localError] using
      norm_add_le
        (primeSeries (localY n (2 * π * (p : ℝ) / q + θ)) -
          Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ))
        (Task52.unitWeightedSum (stdAddChar.mulShift (p : ZMod q)) (localY n θ) - localPhi n q θ)
  have hfac : Real.sqrt n ≤ Real.sqrt q * ((q : ℝ) + Real.sqrt n) := by
    calc
      _ ≤ (q : ℝ) + Real.sqrt n := by linarith [Nat.cast_nonneg (α := ℝ) q]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hsqrt
  have hrem : C * Real.sqrt n * Real.log ((q : ℝ) + 1) ^ A ≤
      C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) * Real.log ((q : ℝ) + 1) ^ A := by
    calc
      _ ≤ C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n)) * Real.log ((q : ℝ) + 1) ^ A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC) (pow_nonneg hlog A)
      _ = _ := by ring
  linarith [htriangle, hr, hbound, hrem]

#print axioms principal_gauss_sum
#print axioms centered_character_expansion
#print axioms prime_unit_correction
#print axioms prime_character_reduction
end LeanLab.HardyLittlewood1923.Decomp448e
