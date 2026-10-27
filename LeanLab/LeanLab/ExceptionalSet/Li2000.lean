/-
P0034 H. Z. Li, The exceptional set of Goldbach numbers (II), Acta Arith. 92 (2000), 71-88.
Unit U-6811, CLOUD 20261021T0117Z-cloud55, track T1. Copy: papers/P0034.pdf, the open ICM scan
matwbn.icm.edu.pl/ksiazki/aa/aa92/aa9217.pdf, with a text layer; page 81 checked on the
rendered page image.

What the paper fixes, by page:
* p. 71, Theorem: for sufficiently large `x`, `E(x) = O(x^{0.914})`, `E(x)` the number of even
  numbers up to `x` that are not a sum of two odd primes.
* p. 81, Section 4: `Y = x^λ` with `λ = 0.0862`, `Q = x^{1-λ}`.
* p. 81, Lemma 7, from Lemma 8 of Chen-Pan 1980: the number `M(x)` of `n ∈ [(1-ε)x, x]` with
  `|D₂(n)| > 0.5 x^{1-10^{-5}λ}` is `≪ x^{1-(1-10^{-4})λ}`.
* p. 87, (6.3): the `n ≤ x` with `(n, q̃) > x^{(1-10^{-4})λ}` number `≤ x^{1-(1-10^{-4})λ+ε}`.
* pp. 86-88, (6.1)-(6.7): every other `n ∈ [(1-ε)x, x]` has `D₁(n) ≥ 0.6 x^{1-10^{-5}λ}`.
So the true exponent of the argument is `1 - (1 - 10^{-4}) · 0.0862 + ε = 0.91380862 + ε`, and
`0.914` is that rounded up; the slack is `0.00019138`.

PROVED here, elementary, zero sorry: the exponent arithmetic; the numerical steps (5.4), (5.6),
(5.8), (6.2), (6.5) and (6.6) from the printed constants; and the reduction of the Theorem to
one named cited input, `WindowInput`, the paper's Sections 2-6 combined as a bound on the
exceptional even `n` in a dyadic block. CONDITIONAL ON `WindowInput`: `li_of_window`,
`li_eventually_of_window`, `li_sharp_of_window`. The dyadic sum is the lab's `T_le` from
`Pintz2018Reduction`, reused, not duplicated.

Faithfulness note: the paper's windows are `[(1-ε)x, x]`; a dyadic block `(Y/2, Y]` is a union
of `O_ε(1)` of them, so `WindowInput` is implied by the paper's per-window bound with a larger
constant. Nothing here proves the analytic content: Lemmas 1-9, the zero-density Lemma 6, the
Tables 1 and 2, and the case values of `I₁, I₂` on p. 84 stay cited.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN; this is an almost-all bound and never reaches a single `n`.
-/
import Mathlib
import LeanLab.ExceptionalSet.Statements
import LeanLab.ExceptionalSet.Pintz2018Reduction

namespace LeanLab.ExceptionalSet.Li2000
open Real Filter Topology LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Pintz2018Reduction

/-- p. 81: `λ = 0.0862`, `Y = x^λ`. -/
noncomputable def lam : ℝ := 0.0862

/-- The exponent the argument gives before `ε`: `1 - (1 - 10^{-4}) λ`, Lemma 7 and (6.3). -/
noncomputable def sharpExponent : ℝ := 1 - (1 - (10 : ℝ)⁻¹ ^ 4) * lam

/-- The exponent arithmetic: `1 - (1 - 10^{-4}) · 0.0862 = 0.91380862 < 0.914`, slack
`0.00019138`, and `1 - 0.914 = 0.086`. -/
theorem exponent_arith :
    sharpExponent = 0.91380862 ∧ sharpExponent < 0.914 ∧ (0.914 : ℝ) - sharpExponent = 0.00019138
      ∧ (1 : ℝ) - 0.914 = 0.086 := by
  unfold sharpExponent lam
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- p. 71 and (6.3): Li improves his own `0.921` of 1999 by `0.007`. -/
theorem improves_li1999 : (0.914 : ℝ) < 0.921 ∧ (0.921 : ℝ) - 0.914 = 0.007 := by
  constructor <;> norm_num

/-- p. 84, the sixteen cases: the printed `(I₁, I₂)` bounds. -/
def caseBounds : List (ℚ × ℚ) :=
  [(0.136, 1.009), (0.143, 1.098), (0.129, 1.177), (0.118, 1.271), (0.114, 1.377),
   (0.118, 1.464), (0.131, 1.374), (0.153, 1.249), (0.185, 1.141), (0.229, 1.047),
   (0.287, 0.967), (0.337, 0.897), (0.372, 0.835), (0.395, 0.784), (0.420, 0.738),
   (0.414, 0.704)]

/-- (5.4): in every case `I₁ I₂ ≤ 0.31062`, the maximum at case 13, so `I₁ I₂ ≤ 0.311`. -/
theorem case_products : ∀ b ∈ caseBounds, b.1 * b.2 ≤ 0.31062 := by
  simp only [caseBounds, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

/-- (5.4) as printed. -/
theorem i1i2_le : ∀ b ∈ caseBounds, b.1 * b.2 ≤ 0.311 :=
  fun b hb => (case_products b hb).trans (by norm_num)

/-- (5.6): with (5.1)'s factor `1 + 2·10^{-5}` on each of `W, W'`, the product stays `≤ 0.311`. -/
theorem w_product : (1 + 2 * (10 : ℝ)⁻¹ ^ 5) ^ 2 * 0.31062 ≤ 0.311 := by norm_num

/-- (5.8) from (5.7): `0.0107 · 0.884 ≤ 0.0095`. -/
theorem w_product_exc : (0.0107 : ℝ) * 0.884 ≤ 0.0095 := by norm_num

/-- p. 86, no exceptional character: `0.6601 - 2.0797 · 0.311 - 10^{-9} ≥ 0.01`. -/
theorem no_exc_main : (0.6601 : ℝ) - 2.0797 * 0.311 - (10 : ℝ)⁻¹ ^ 9 ≥ 0.01 := by norm_num

/-- (6.2): `0.6601 - 2.0797 · 0.0095 - 10^{-8} - 4.1594 · 0.0107 ≥ 0.59`. -/
theorem case1_main :
    (0.6601 : ℝ) - 2.0797 * 0.0095 - (10 : ℝ)⁻¹ ^ 8 - 4.1594 * 0.0107 ≥ 0.59 := by norm_num

/-- (6.5): `1 - 0.8905 = 0.1095` and `0.1095 · 0.6601 - 2.0797 · 0.0095 - 10^{-8} - 4.1594 ·
0.0107 ≥ 0.007`. -/
theorem case3_main : (1 : ℝ) - 0.8905 = 0.1095 ∧
    (0.1095 : ℝ) * 0.6601 - 2.0797 * 0.0095 - (10 : ℝ)⁻¹ ^ 8 - 4.1594 * 0.0107 ≥ 0.007 := by
  constructor <;> norm_num

/-- (6.6): `0.62 - 2.0797 · 10^{-7} - (8 + 4.1594) · 10^{-8} ≥ 0.6`. -/
theorem case3_siegel : (0.62 : ℝ) - 2.0797 * (10 : ℝ)⁻¹ ^ 7 - (8 + 4.1594) * (10 : ℝ)⁻¹ ^ 8 ≥ 0.6 := by
  norm_num

/-- Lemma 7's threshold is beaten: `0.6 x^{1-ε} > 0.5 x^{1-10^{-5}λ}` once `ε < 10^{-5}λ`;
the exponent gap `10^{-5} λ` is positive. -/
theorem threshold_gap : (0 : ℝ) < (10 : ℝ)⁻¹ ^ 5 * lam ∧ (0.5 : ℝ) < 0.6 := by
  unfold lam; constructor <;> norm_num

/-! ### The reduction to one cited input -/

/-- **Cited input**, Li 2000 Sections 2-6, Lemma 7 and (6.1)-(6.7) combined: for every
`ε > 0` the exceptional even `n` in the dyadic block `(⌊Y/2⌋, Y]` number `≤ C Y^{0.91380862 + ε}`
for `Y` beyond some `Y₀`. -/
def WindowInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ Y0 : ℕ, ∀ Y : ℕ, Y0 < Y →
    (D Exc Y : ℝ) ≤ C * (Y : ℝ) ^ (sharpExponent + ε)

/-- Dyadic summation to the lab's `PowerBound`, for any exponent `α > 0`. -/
theorem powerBound_of_blocks {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {Y0 : ℕ}
    (h : ∀ Y : ℕ, Y0 < Y → (D Exc Y : ℝ) ≤ C * (Y : ℝ) ^ α) : PowerBound α := by
  refine ⟨C / (1 - (2 : ℝ) ^ (-α)) + T Exc Y0, fun X hX => ?_⟩
  have hb := T_le Exc hα hC h X
  have h1 : (1 : ℝ) ≤ (X : ℝ) ^ α :=
    one_le_rpow (by exact_mod_cast hX) hα.le
  have hT0 : (0 : ℝ) ≤ T Exc Y0 := Nat.cast_nonneg _
  rw [E_eq_T]
  nlinarith

/-- CONDITIONAL ON `WindowInput`: `E X ≪ X^{0.91380862 + ε}` for every `ε > 0`, the form the
proof actually gives. -/
theorem li_sharp_of_window (h : WindowInput) :
    ∀ ε : ℝ, 0 < ε → PowerBound (sharpExponent + ε) := by
  intro ε hε
  obtain ⟨C, hC, Y0, hY⟩ := h ε hε
  have hs : (0 : ℝ) < sharpExponent := by unfold sharpExponent lam; norm_num
  exact powerBound_of_blocks (by linarith) hC hY

/-- CONDITIONAL ON `WindowInput`: the paper's Theorem, `E X ≪ X^{0.914}`, the lab's `li`. -/
theorem li_of_window (h : WindowInput) : PowerBound 0.914 := by
  have := li_sharp_of_window h 0.00019138 (by norm_num)
  have he : sharpExponent + 0.00019138 = 0.914 := by unfold sharpExponent lam; norm_num
  rwa [he] at this

/-- CONDITIONAL ON `WindowInput`: the eventual form `E X < X^{0.914}` for all large `X`, with no
constant, which Pintz 2018 eq (1.7) quotes; the slack `0.00019138` absorbs the constant. -/
theorem li_eventually_of_window (h : WindowInput) : EventuallyBelow 0.914 := by
  obtain ⟨C, _, Y0, hY⟩ := h 0.0001 (by norm_num)
  have hβ : (0 : ℝ) ≤ sharpExponent + 0.0001 := by unfold sharpExponent lam; norm_num
  have hβα : sharpExponent + 0.0001 < 0.914 := by unfold sharpExponent lam; norm_num
  obtain ⟨X0, hX0⟩ := eventually_lt_of_bigO Exc hβ hβα hY
  exact ⟨X0, fun X hX => by rw [E_eq_T]; exact hX0 X hX⟩

/-- Vacuity test: the block hypothesis shape is satisfiable, for the empty predicate. -/
theorem vacuity_blocks (α : ℝ) :
    ∀ Y : ℕ, 0 < Y → (D (fun _ => False) Y : ℝ) ≤ 0 * (Y : ℝ) ^ α := by
  intro Y _
  simp [D]

end LeanLab.ExceptionalSet.Li2000

#print axioms LeanLab.ExceptionalSet.Li2000.exponent_arith
#print axioms LeanLab.ExceptionalSet.Li2000.improves_li1999
#print axioms LeanLab.ExceptionalSet.Li2000.case_products
#print axioms LeanLab.ExceptionalSet.Li2000.i1i2_le
#print axioms LeanLab.ExceptionalSet.Li2000.w_product
#print axioms LeanLab.ExceptionalSet.Li2000.w_product_exc
#print axioms LeanLab.ExceptionalSet.Li2000.no_exc_main
#print axioms LeanLab.ExceptionalSet.Li2000.case1_main
#print axioms LeanLab.ExceptionalSet.Li2000.case3_main
#print axioms LeanLab.ExceptionalSet.Li2000.case3_siegel
#print axioms LeanLab.ExceptionalSet.Li2000.threshold_gap
#print axioms LeanLab.ExceptionalSet.Li2000.powerBound_of_blocks
#print axioms LeanLab.ExceptionalSet.Li2000.li_sharp_of_window
#print axioms LeanLab.ExceptionalSet.Li2000.li_of_window
#print axioms LeanLab.ExceptionalSet.Li2000.li_eventually_of_window
#print axioms LeanLab.ExceptionalSet.Li2000.vacuity_blocks
