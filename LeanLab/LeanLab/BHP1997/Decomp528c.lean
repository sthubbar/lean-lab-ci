/-
P0069, pages 24 to 27, display 4.1. CODEX task528.
An explicit finite prefix envelope controls the tapered polynomial.
Its mean value estimate is retained as an explicit hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp528b

namespace LeanLab.BHP1997.Decomp528c
open Classical Decomp528a Decomp528b Decomp312c
open scoped BigOperators

/-- Page 24, auxiliary initial sums on the actual polynomial support. -/
noncomputable def prefixPolynomial (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range j,
    if ⌊x / 2⌋₊ < k then (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ s else 0

/-- Page 24, auxiliary maximal initial sum norm over the finite support. -/
noncomputable def prefixEnvelope (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℝ :=
  (Finset.range (⌊2 * x⌋₊ + 2)).sup' (by simp) (fun j => ‖prefixPolynomial a x χ s j‖)

/-- Page 24, the maximal initial sum norm bounds each permitted prefix. -/
theorem prefix_le_envelope (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) {j : ℕ} (hj : j ≤ ⌊2 * x⌋₊ + 1) :
    ‖prefixPolynomial a x χ s j‖ ≤ prefixEnvelope a x χ s := by
  exact Finset.le_sup' (fun j => ‖prefixPolynomial a x χ s j‖)
    (show j ∈ Finset.range (⌊2 * x⌋₊ + 2) from Finset.mem_range.mpr (by omega))

/-- Page 24, the maximal initial sum norm is nonnegative. -/
theorem prefixEnvelope_nonneg (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : 0 ≤ prefixEnvelope a x χ s :=
  (norm_nonneg (prefixPolynomial a x χ s 0)).trans (prefix_le_envelope a x χ s (by omega))

/-- Page 24, each finite initial sum is continuous in signed height. -/
theorem prefixPolynomial_continuous (a : ℝ → ℕ → ℝ) (x σ : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (j : ℕ) :
    Continuous (fun t : ℝ => prefixPolynomial a x χ (Thm4.half (σ * t)) j) := by
  unfold prefixPolynomial
  apply continuous_finsetSum
  intro k hk
  split_ifs with h
  · have hk0 : k ≠ 0 := by omega
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    have hh : Continuous (fun t : ℝ => Thm4.half (σ * t)) := by unfold Thm4.half; fun_prop
    exact continuous_const.div (hh.const_cpow (Or.inl hkC))
      (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hkC))
  · exact continuous_const

/-- Page 24, the finite maximum envelope is continuous in signed height. -/
theorem prefixEnvelope_continuous (a : ℝ → ℕ → ℝ) (x σ : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => prefixEnvelope a x χ (Thm4.half (σ * t))) := by
  exact Continuous.finset_sup'_apply _ (fun j hj => (prefixPolynomial_continuous a x σ χ j).norm)

/-- Page 24, the prefix envelope controls the exact tapered polynomial by factor three. -/
theorem tapered_polynomial_le (a : ℝ → ℕ → ℝ) {x : ℝ} (hx : 0 < x)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (tapered a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ s‖ ≤
      3 * prefixEnvelope a x χ s := by
  have he : (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun k => ⌊x / 2⌋₊ < k) =
      Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  have h := tapered_sum_norm_le hx
    (fun k => if ⌊x / 2⌋₊ < k then (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ s else 0)
    (⌊2 * x⌋₊ + 1) (prefixEnvelope_nonneg a x χ s)
    (fun j hj => prefix_le_envelope a x χ s hj)
  have hs : (∑ k ∈ Finset.range (⌊2 * x⌋₊ + 1), (taper x k : ℂ) *
      (if ⌊x / 2⌋₊ < k then (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ s else 0)) =
      ∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (tapered a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ s := by
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter, he]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [tapered, Complex.ofReal_mul]
    ring
  rwa [hs] at h

/-- Page 24, display 4.1, finite maximal partial summation reduction.
CONDITIONAL on the explicit analytic mean value for the prefix envelope.
This transfers the estimate and does not assert that arithmetic input. -/
theorem meanValue41_of_prefix_envelope (ε : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ σ ∈ ({-1, 1} : Finset ℝ),
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
          prefixEnvelope a x χ (Thm4.half (σ * t))) ≤
          C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) : MeanValue41 ε (tapered a) := by
  intro A hA
  obtain ⟨C, X, h⟩ := ha A hA
  refine ⟨3 * |C|, max X 1, ?_⟩
  intro x hx q hq hqx χ σ hσ
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  let L := Real.exp (Real.log x ^ (1 / 3 : ℝ))
  let U := x ^ (0.45 - 2 * ε / 3)
  have hc : Continuous (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (tapered a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖) := by
    apply Continuous.norm
    apply continuous_finsetSum
    intro k hk
    have hk0 : k ≠ 0 := by have := (Finset.mem_Ioc.mp hk).1; omega
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    have hh : Continuous (fun t : ℝ => Thm4.half (σ * t)) := by unfold Thm4.half; fun_prop
    exact continuous_const.div (hh.const_cpow (Or.inl hkC))
      (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hkC))
  by_cases hlu : L ≤ U
  · have hi := intervalIntegral.integral_mono (μ := MeasureTheory.volume) hlu (hc.intervalIntegrable L U)
      (((prefixEnvelope_continuous a x σ χ).const_mul 3).intervalIntegrable L U)
      (fun t => tapered_polynomial_le a hx0 χ (Thm4.half (σ * t)))
    rw [intervalIntegral.integral_const_mul] at hi
    have hb := h x ((le_max_left _ _).trans hx) q hq hqx χ σ hσ
    change (∫ t in L..U, prefixEnvelope a x χ (Thm4.half (σ * t))) ≤ _ at hb
    calc
      _ ≤ 3 * (∫ t in L..U, prefixEnvelope a x χ (Thm4.half (σ * t))) := hi
      _ ≤ 3 * (C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := by gcongr
      _ ≤ (3 * |C|) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
        have hs : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
          mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg (Real.log_nonneg hx1) _)
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) hs]
  · have hi : (∫ t in L..U, ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (tapered a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hlu) (fun t => norm_nonneg _))
    exact hi.trans (mul_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg hx0.le _))
      (Real.rpow_nonneg (Real.log_nonneg hx1) _))

end LeanLab.BHP1997.Decomp528c
