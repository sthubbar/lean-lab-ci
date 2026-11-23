import Mathlib
import LeanLab.HelfgottMajor.PVOddCot1122
import LeanLab.HelfgottMajor.PVOddTrunc1122

/-!
Route burst S68, burst-20261122, tag odd-truncated, third file.
The LEAF `PVOddTrunc1122.odd_cot_bound` from the PROVED finite Polya identity
`PVOddCot1122.polya_interval_cot`, the Gauss sum norm `PV420Split1122.norm_gauss`, and one
smaller LEAF, `cot_sum_fold`: for odd χ the terms h and -h pair to cosine differences, and the
sum over ZMod q folds onto 1 ≤ h ≤ (q-1)/2. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddCotBound1122

open Real Finset

/-- LEAF: Pomerance 2011 proof of Theorem 1 for odd χ, Frolenkov display 14 step: in the
cotangent form of the Polya identity, for odd χ the terms h and -h pair, since χ⁻¹(-h) = -χ⁻¹(h)
and cot(π(q-h)/q) = -cot(π h/q), so the sum equals the sum of χ⁻¹(h) cot(π h/q) times
2(cos hβ - cos hα)/2; its norm is at most the sum over h ≠ 0 of |cot(π h/q)| |cos hα - cos hβ|,
which folds onto 1 ≤ h ≤ (q-1)/2 with factor 2, the term h = q/2 for even q being 0.
Screened with Python for odd primitive χ, 7 ≤ q < 60, M < q, N < q + 3: no violation, slack 0 up
to rounding. Class EASY. -/
theorem cot_sum_fold {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)‖ ≤
      2 * ∑ m ∈ Icc 1 ((q - 1) / 2),
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  sorry

/-- The sum on the right of `odd_cot_bound` is nonnegative, cot being positive on (0, π/2).
PROVED. -/
theorem fold_nonneg {q : ℕ} (M N : ℕ) :
    0 ≤ ∑ m ∈ Icc 1 ((q - 1) / 2),
      Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  refine sum_nonneg fun m hm => mul_nonneg ?_ (abs_nonneg _)
  rw [mem_Icc] at hm
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : (2 : ℝ) * m < q := by exact_mod_cast (show 2 * m < q by omega)
  have hx0 : 0 < π * m / q := by positivity
  have hx1 : π * m / q < π / 2 := by
    rw [div_lt_div_iff₀ hq (by norm_num)]
    nlinarith [pi_pos]
  rw [Real.cot_eq_cos_div_sin]
  exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hx1.le⟩)
    (Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith))

/-- Exactly `PVOddTrunc1122.odd_cot_bound`, from `PVOddCot1122.polya_interval_cot`,
|τ(χ⁻¹)| = √q, |χ| ≤ 1, and the LEAF `cot_sum_fold`. PROVED from the LEAF. -/
theorem odd_cot_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + 1 / sqrt q * ∑ m ∈ Icc 1 ((q - 1) / 2),
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  set T := ∑ m ∈ Icc 1 ((q - 1) / 2),
    Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| with hT
  have hT0 : 0 ≤ T := fold_nonneg M N
  have hsq : 0 < sqrt (q : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
  by_cases hMN : M ≤ N + 1
  · have hid := LeanLab.HelfgottMajor.PVOddCot1122.polya_interval_cot hχ (by omega) hMN
    have hτ := LeanLab.HelfgottMajor.PV420Split1122.norm_gauss
      (LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ)
    have hF := cot_sum_fold χ hq7 hodd M N
    set τ := gaussSum χ⁻¹ ZMod.stdAddChar
    set S := ∑ m ∈ Icc M N, χ (m : ZMod q)
    set F := ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)
    have h1 : ‖χ ((N + 1 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : ‖χ (M : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have hn : ‖τ * S‖ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by
      rw [hid]
      calc ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)) - Complex.I / 2 * F‖
          ≤ ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q))‖ +
            ‖Complex.I / 2 * F‖ := norm_sub_le _ _
        _ ≤ 1 / 2 * ‖τ‖ * (‖χ ((N + 1 : ℕ) : ZMod q)‖ + ‖χ (M : ZMod q)‖) + 1 / 2 * ‖F‖ := by
          gcongr
          · rw [norm_mul, norm_mul, norm_neg]
            gcongr
            · simp
            · exact norm_sub_le _ _
          · rw [norm_mul, norm_div, Complex.norm_I]; simp
        _ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by nlinarith [norm_nonneg τ]
    rw [norm_mul, hτ] at hn
    have : sqrt q * ‖S‖ ≤ sqrt q * (1 + 1 / sqrt q * T) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_one_div_cancel hsq.ne', one_mul]
      linarith
    exact le_of_mul_le_mul_left this hsq
  · have he : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he, sum_empty, norm_zero]
    have : 0 ≤ 1 / sqrt (q : ℝ) * T := mul_nonneg (by positivity) hT0
    linarith

example : type_of% @odd_cot_bound =
    type_of% @LeanLab.HelfgottMajor.PVOddTrunc1122.odd_cot_bound := rfl

end LeanLab.HelfgottMajor.PVOddCotBound1122

#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.cot_sum_fold
#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.fold_nonneg
#print axioms LeanLab.HelfgottMajor.PVOddCotBound1122.odd_cot_bound
