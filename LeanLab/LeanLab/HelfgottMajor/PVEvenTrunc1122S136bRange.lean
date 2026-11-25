import Mathlib
import LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail

/-!
Route burst S136 round 2, burst-20261122, step even-truncated-p3.
Split of the HARD LEAF `PVEvenTrunc1122S124Tail.cot_tail_large` at the explicit cut Q0 = 10000.

For 64 < q ≤ 10000 the TRIVIAL bound suffices: drop the character and the sine, so the norm of the
tail is at most the sum of |cot (π h / q)| over H < h < q - H, see `tail_le_trivial`, PROVED here.
A python screen in round 1 found an H near 0.32 q making the inequality hold for every q from 65 to
10000, best margins 3.63 at q = 65, 10.9 at q = 1000, 18.1 at q = 10000; that finite check is the
LEAF `cot_tail_range`, class MEDIUM. For q above 10000 the trivial route fails from about 10^5 on,
and the tail needs cancellation in the character sum, Pomerance 2011, Integers 11A, Article A19,
proof of Theorem 1, Abel summation against partial character sums, and Frolenkov display 17: the
LEAF `cot_tail_huge`, class HARD.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange

open Real Finset

/-- The trivial bound: the norm of the cotangent tail is at most the sum of |cot (π h / q)| over the
tail range, since |χ⁻¹ h| ≤ 1 and |sin| ≤ 1. PROVED. -/
theorem tail_le_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H K : ℕ) :
    ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ ≤
      ∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)),
        |cot (π * (h.val : ℝ) / q)| := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have h1 : ‖χ⁻¹ h‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : |sin (2 * π * K * (h.val : ℝ) / q)| ≤ 1 := abs_sin_le_one _
  have h3 : 0 ≤ |cot (π * (h.val : ℝ) / q)| := abs_nonneg _
  have h4 : 0 ≤ ‖χ⁻¹ h‖ := norm_nonneg _
  calc ‖χ⁻¹ h‖ * (|cot (π * (h.val : ℝ) / q)| * |sin (2 * π * K * (h.val : ℝ) / q)|)
      ≤ 1 * (|cot (π * (h.val : ℝ) / q)| * 1) := by gcongr
    _ = |cot (π * (h.val : ℝ) / q)| := by ring

/-- LEAF: cot_tail_large for 64 < q ≤ 10000, by the trivial bound `tail_le_trivial` and a finite
check of the sum of |cot (π h / q)| for H < h < q - H with H near 0.32 q against the budget; the
round 1 python screen of S136 found such an H for every q in range. Class MEDIUM. Pomerance 2011,
Integers 11A, A19, Theorem 1 even case; Frolenkov displays 15 to 17. -/
theorem cot_tail_range {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (hbig : 64 < q) (hle : q ≤ 10000) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  sorry

/-- LEAF: cot_tail_large for q above 10000, where the trivial bound fails from about q = 10^5 on
and the tail needs cancellation in the character sum: Pomerance 2011, Integers 11A, A19, proof of
Theorem 1, Abel summation against partial sums of χ, and Frolenkov display 17. Class HARD. -/
theorem cot_tail_huge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (hbig : 10000 < q) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  sorry

/-- Assembly: exactly `PVEvenTrunc1122S124Tail.cot_tail_large`, from the LEAFs `cot_tail_range`
and `cot_tail_huge`. -/
theorem cot_tail_large_of_leaves {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (hbig : 64 < q) :
    ∃ H : ℕ, 1 ≤ H ∧ 2 * H < q ∧ ∀ K : ℕ,
      ‖∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
          ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
          (2 * sqrt q) + 1 / 2 ≤
        1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
  by_cases hle : q ≤ 10000
  · exact cot_tail_range χ hχ hq heven hbig hle
  · exact cot_tail_huge χ hχ hq heven (by omega)

example : type_of% @cot_tail_large_of_leaves =
    type_of% @LeanLab.HelfgottMajor.PVEvenTrunc1122S124Tail.cot_tail_large := rfl

end LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange

#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange.tail_le_trivial
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange.cot_tail_range
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange.cot_tail_huge
#print axioms LeanLab.HelfgottMajor.PVEvenTrunc1122S136bRange.cot_tail_large_of_leaves
