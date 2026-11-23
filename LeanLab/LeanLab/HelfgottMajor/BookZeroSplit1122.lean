import LeanLab.HelfgottMajor.ZeroCount1623
import Mathlib

/-!
# Split of `ZeroCount1623.book_zero_count`, burst-20261122, tag book-zero-count-split

Source traced: Helfgott, The ternary Goldbach problem, book draft Part I of 2019-12-15,
webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf, section 3.7.3.3, display 3.95, page 86.
The book proves 3.95 for primitive NON-TRIVIAL chi and T at least 1 by citing
Trudgian 2015b Thm 1 with eta = 0.20 of Table 1, halved per its footnote 5, and then extends it
to the trivial character by displays 3.62 and 3.63 and the height 14.13472 of the first zero.

This file follows exactly that structure:
* `book_395_nontrivial`, LEAF HARD, display 3.95 as printed for chi non-trivial.
* `zeta_first_zero`, LEAF MEDIUM, the first zero of zeta has height 14.13472.
* `zeta_362_363_first`, `zeta_362_363_second`, LEAF HARD, display 3.62 combined with each
  line of display 3.63.
* The combination for the trivial character is PROVED here, including the arithmetic that turns
  3.62 and 3.63 into 0.15 log T + 3.389, with a cut at log T = 25.5.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BookZeroSplit1122
open LeanLab.HelfgottMajor.ZeroCount1623

variable {q : ℕ} [NeZero q]

/-- LEAF: book display 3.95, section 3.7.3.3, page 86 of Part I, for chi primitive and
NON-TRIVIAL and T at least 1. Class HARD. The book cites Trudgian 2015b Thm 1, arXiv 1206.1844,
with the eta = 0.20 constants of its Table 1, halved by footnote 5, which says a look at
Trudgian section 2 suffices to bound the one sided count by half of his two sided bound.
QUESTION: the constants 0.300 and 6.778 halved to 0.15 and 3.389 are those of arXiv 1206.1844v1;
v2 Table 1 gives 0.298 and 6.828 at eta = 0.20, whose half 0.149 log qT + 3.414 does not imply
this leaf for qT below e^25. Bennett, Martin, O'Bryant, Rechnitzer, arXiv 2005.02989, report a
gap in Trudgian's proof. The halving of footnote 5 is asserted, not proved, in the book. -/
theorem book_395_nontrivial (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  sorry

/-- LEAF: book section 3.7.3.3, page 86, the first non-trivial zero of zeta has imaginary part
14.13472..., cited there to Gra03 and Edw74 section 6.1. Stated with the weaker constant 14.13.
Class MEDIUM: a finite verified computation. -/
theorem zeta_first_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (14.13 : ℝ) < |ρ.im| := by
  sorry

/-- LEAF: book display 3.62, page 73 of Part I, combined with the FIRST line of display 3.63,
Trudgian 2012 Thm 1, abs S of T at most 0.17 log T + 1.998 for T at least e.
For chi mod 1 the L-function is zeta, so bookCount is the book N of T with the half convention
of section 3.5. Stated on T at least 14.13, inside the book range.
Class HARD. QUESTION: 3.62 is derived in the book assuming no zero at height T; the half
convention at a zero height is the limit form, not checked here. -/
theorem zeta_362_363_first (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 14.13 ≤ T) :
    |bookCount χ T - bookMain 1 T - 7 / 8| ≤
      0.17 * Real.log T + 1.998 + 5 / (48 * Real.pi * T) + 0.068 / T ^ 3 := by
  sorry

/-- LEAF: book display 3.62, page 73 of Part I, combined with the SECOND line of display 3.63,
Trudgian 2014 Thm 1, abs S of T at most 0.112 log T + 0.278 log log T + 2.51 for T at least e.
Stated on T at least 14.13. Class HARD. Same QUESTION as `zeta_362_363_first`. -/
theorem zeta_362_363_second (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 14.13 ≤ T) :
    |bookCount χ T - bookMain 1 T - 7 / 8| ≤
      0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.51 +
        5 / (48 * Real.pi * T) + 0.068 / T ^ 3 := by
  sorry

/-! ### Proved pieces -/

/-- In the band T at most 2 pi e the main term for q = 1 lies in the interval from -1 to 0. -/
theorem bookMain_one_band {T : ℝ} (hT : 1 ≤ T) (hb : T ≤ 2 * Real.pi * Real.exp 1) :
    -1 ≤ bookMain 1 T ∧ bookMain 1 T ≤ 0 := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  set x := T / (2 * Real.pi) with hx
  have hxpos : 0 < x := by positivity
  have hmain : bookMain 1 T = x * (Real.log x - 1) := by
    unfold bookMain
    rw [Nat.cast_one, one_mul,
      show T / (2 * Real.pi * Real.exp 1) = T / (2 * Real.pi) / Real.exp 1 by rw [div_div],
      Real.log_div (by positivity) he.ne', Real.log_exp]
  have hxe : x ≤ Real.exp 1 := by
    rw [hx, div_le_iff₀ (by positivity)]; linarith
  have hlog1 : Real.log x ≤ 1 := by
    have := Real.log_le_log hxpos hxe
    rwa [Real.log_exp] at this
  have hlow := Real.one_sub_inv_le_log_of_pos hxpos
  have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hxpos.ne'
  rw [hmain]
  constructor
  · nlinarith
  · nlinarith

/-- log 25.5 is at most 3.25. -/
theorem log_25_5_le : Real.log 25.5 ≤ 3.25 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have hsplit : Real.exp 3.25 = Real.exp 1 ^ 3 * Real.exp 0.25 := by
    rw [show (3.25 : ℝ) = ((3 : ℕ) : ℝ) * 1 + 0.25 by norm_num, Real.exp_add, Real.exp_nat_mul]
  rw [hsplit]
  have he := Real.exp_one_gt_d9
  have he3 : (2.718 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hq := Real.quadratic_le_exp_of_nonneg (x := (0.25 : ℝ)) (by norm_num)
  have h3 : (0 : ℝ) ≤ Real.exp 1 ^ 3 := by positivity
  nlinarith

/-- The trivial character case, PROVED from the three zeta LEAFs. This is the book sentence
after 3.95: by 3.62, 3.63 and the first zero, 3.95 also holds for chi trivial and T at least 1. -/
theorem zeta_case (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain 1 T| ≤ bookError 1 T := by
  have hpi := Real.pi_gt_three
  have he := Real.exp_one_gt_d9
  have hErr : bookError 1 T = 0.15 * Real.log T + 3.389 := by
    simp only [bookError, Nat.cast_one, one_mul]
  rw [hErr]
  rcases le_or_gt T 14.13 with hlo | hhi
  · -- No zero below 14.13, and the main term is in [-1, 0].
    have hN : bookCount χ T = 0 := by
      unfold bookCount
      refine Finset.sum_eq_zero fun ρ hρ => ?_
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
      simp only [stripZeros, Set.mem_ofPred_eq] at hρ
      obtain ⟨⟨hz, hre0, hre1, him⟩, _⟩ := hρ
      rw [DirichletCharacter.LFunction_modOne_eq] at hz
      have := zeta_first_zero hz hre0 hre1
      exfalso; linarith
    have hb : T ≤ 2 * Real.pi * Real.exp 1 := by nlinarith
    obtain ⟨m1, m2⟩ := bookMain_one_band hT hb
    have hL := Real.log_nonneg hT
    rw [hN, abs_le]
    constructor <;> linarith
  · have hT14 : (14.13 : ℝ) ≤ T := hhi.le
    have hTpos : 0 < T := by linarith
    have t1 : 5 / (48 * Real.pi * T) ≤ 0.00246 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have t2 : 0.068 / T ^ 3 ≤ 0.00004 := by
      rw [div_le_iff₀ (by positivity)]
      have : (14.13 : ℝ) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by norm_num) hT14 3
      nlinarith
    have t1' : 0 ≤ 5 / (48 * Real.pi * T) := by positivity
    have t2' : 0 ≤ 0.068 / T ^ 3 := by positivity
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT
    rcases le_or_gt (Real.log T) 25.5 with hs | hl
    · obtain ⟨a1, a2⟩ := abs_le.mp (zeta_362_363_first χ hT14)
      rw [abs_le]
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := abs_le.mp (zeta_362_363_second χ hT14)
      have hLpos : 0 < Real.log T := by linarith
      have hdiv := Real.log_le_sub_one_of_pos (x := Real.log T / 25.5) (by positivity)
      rw [Real.log_div hLpos.ne' (by norm_num)] at hdiv
      have h255 := log_25_5_le
      have h' : Real.log T / 25.5 = Real.log T * (2 / 51) := by
        rw [div_eq_mul_inv]; norm_num
      rw [h'] at hdiv
      have hlogL : Real.log (Real.log T) ≤ 2.25 + Real.log T * (2 / 51) := by linarith
      have hlogL0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
      rw [abs_le]
      constructor <;> linarith

/-- ASSEMBLY. Exactly the sealed statement `ZeroCount1623.book_zero_count`, proved from the
LEAFs above by the book's own case split: chi non-trivial is display 3.95, chi trivial forces
q = 1 for a primitive character and is `zeta_case`. -/
theorem book_zero_count_assembled (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ}
    (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  by_cases h1 : χ = 1
  · have hq : q = 1 := by
      have h := (DirichletCharacter.isPrimitive_def χ).mp hχ
      rw [h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hq
    exact zeta_case χ hT
  · exact book_395_nontrivial χ hχ h1 hT

example : type_of% @book_zero_count_assembled = type_of% @ZeroCount1623.book_zero_count := rfl

end LeanLab.HelfgottMajor.BookZeroSplit1122

#print axioms LeanLab.HelfgottMajor.BookZeroSplit1122.book_zero_count_assembled
#print axioms LeanLab.HelfgottMajor.BookZeroSplit1122.zeta_case
#print axioms LeanLab.HelfgottMajor.BookZeroSplit1122.bookMain_one_band
#print axioms LeanLab.HelfgottMajor.BookZeroSplit1122.log_25_5_le
