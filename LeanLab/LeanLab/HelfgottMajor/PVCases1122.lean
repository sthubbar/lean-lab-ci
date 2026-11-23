import Mathlib
import LeanLab.HelfgottMajor.PV420Split1122

/-!
Route burst S58 round two, burst-20261122, tag pomerance-cases.
Split of the HARD case LEAFs `PV420Split1122.pomerance_even_case` and
`PV420Split1122.pomerance_odd_case`, Pomerance 2011 Theorem 1, along the structure that
Frolenkov arXiv 1107.0381 Sections 3 and 5 follows: Fourier expansion of the interval
indicator, display 12; truncation at a parameter, display 15 and 16; reduction through
Pomerance display 10, Frolenkov display 14, and |τ(χ)| = √q, display 13, to the sum of
|sin| or of |cos mα - cos mβ|, displays 17 and 22; application of Pomerance Lemma 3 or
Section 4; and, for even χ, the doubling S_χ = 2 T_χ of Frolenkov display 1.

Pomerance's own truncation error and choice of H are not quoted by Frolenkov, who uses
Bykovskii smoothing instead, and the Integers PDF is not reachable. So the truncation step
is a LEAF that asserts: at Pomerance's H, the truncated expansion with its error fits the
part of the final bound not used by Lemma 3 or Section 4. Everything else is PROVED here:
the even reduction of intervals to initial segments, the application of Lemma 3 and of
Section 4, and the final arithmetic.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVCases1122

open Real Finset

/-- Frolenkov display 1, the easy half, used by Pomerance for even χ: an interval sum is a
difference of two initial segment sums, so it is at most the sum of their norms. PROVED. -/
theorem interval_le_two_initial {q : ℕ} (χ : DirichletCharacter ℂ q) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      ‖∑ m ∈ range (N + 1), χ (m : ZMod q)‖ + ‖∑ m ∈ range M, χ (m : ZMod q)‖ := by
  by_cases h : M ≤ N + 1
  · have : ∑ m ∈ Icc M N, χ (m : ZMod q) =
        ∑ m ∈ range (N + 1), χ (m : ZMod q) - ∑ m ∈ range M, χ (m : ZMod q) := by
      have hI : Icc M N = Ico M (N + 1) := by ext x; simp
      rw [← Finset.sum_Ico_eq_sub _ h, hI]
    rw [this]; exact norm_sub_le _ _
  · have : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, sum_empty, norm_zero]; positivity

/-- LEAF: Pomerance 2011, proof of Theorem 1 for even χ, the steps before Lemma 3:
the Polya Fourier expansion of the initial segment indicator, Frolenkov display 12 with M = 0,
truncated at Pomerance's parameter H with his explicit truncation error, Frolenkov displays 15
and 16, then reduced through display 10 and |τ(χ)| = √q, Frolenkov displays 13, 14 and 17, to
√q/π times the sum of |sin(j x)|/j at x = 2πK/q; with Pomerance's choice of H the truncation
error fits in what the final bound leaves after Lemma 3. Class HARD. -/
theorem even_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  sorry

/-- Pomerance even case, initial segments: Lemma 3 applied to the truncated sum, then the
final arithmetic, giving T_χ at most half of Pomerance's even bound. PROVED from the LEAF
`even_truncated` and the hypothesis Lemma 3. -/
theorem even_initial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hL3 : ∀ (x : ℝ) (n : ℕ), 1 ≤ n → ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n))
    (htr : ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)))
    (K : ℕ) :
    ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
      1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q := by
  obtain ⟨H, hH, hK⟩ := htr
  have h1 := hK K
  have h2 := (hL3 (2 * π * K / q) H hH).le
  have hc : 0 ≤ sqrt q / π := div_nonneg (sqrt_nonneg _) pi_pos.le
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  have hpi : π ≠ 0 := pi_pos.ne'
  have e : sqrt q / π * (2 / π * log H + 2 / π * (eulerMascheroniConstant + log 2 + 3 / H)) =
      2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H) := by
    field_simp; ring
  linarith

/-- LEAF: Pomerance 2011, proof of Theorem 1 for odd χ, the steps before Section 4: the Polya
Fourier expansion of the interval indicator, Frolenkov display 12, truncated at Pomerance's
parameter H with his explicit truncation error, Frolenkov displays 15 and 21, then reduced
through display 10 and |τ(χ)| = √q, Frolenkov displays 13, 14 and 22, to √q/π times the sum of
|cos mα - cos mβ|/m at α = 2πM/q, β = 2π(N+1)/q; with Pomerance's choice of H the truncation
error fits in what the final bound leaves after Section 4. Class HARD.
REPAIR S58: 7 ≤ q added; FALSE without it at q = 3, M = N = 1, see the notes. -/
theorem odd_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  sorry

/-- Pomerance odd case: Section 4 applied to the truncated sum, then the final arithmetic.
PROVED from the LEAF `odd_truncated` and the hypothesis Section 4. -/
theorem odd_from_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (htr : ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)))
    (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  obtain ⟨H, hH, hK⟩ := htr
  have h1 := hK M N
  have h2 := (hS4 (2 * π * M / q) (2 * π * (N + 1) / q) H hH).le
  have hc : 0 ≤ sqrt q / π := div_nonneg (sqrt_nonneg _) pi_pos.le
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- Assembly: exactly `PV420Split1122.pomerance_even_case`, from `interval_le_two_initial`,
`even_initial` and the LEAF `even_truncated`. -/
theorem pomerance_even_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hL3 : ∀ (x : ℝ) (n : ℕ), 1 ≤ n → ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n))
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) + ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (heven : χ (-1) = 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  have htr := even_truncated χ hχ hq heven
  have a := even_initial χ hL3 htr (N + 1)
  have b := even_initial χ hL3 htr M
  have c := interval_le_two_initial χ M N
  have e : 2 * (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q) =
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by ring
  linarith

example : type_of% @pomerance_even_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_even_case := rfl

/-- LEAF: Pomerance 2011 Theorem 1, odd case, for the small moduli q below 7 left out of
`odd_truncated`: q = 3, 4, 5, since q = 6 has no primitive character. A finite check of the
interval sums over one period, the largest norm being at most 2 against a bound above 2.08.
Class EASY. -/
theorem odd_small {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (hq7 : q < 7) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- Assembly: exactly `PV420Split1122.pomerance_odd_case`, from `odd_from_truncated` and the
LEAF `odd_truncated` for q at least 7, and the LEAF `odd_small` below 7. -/
theorem pomerance_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q :=
  if h7 : 7 ≤ q then odd_from_truncated χ hS4 (odd_truncated χ hχ h7 hodd) M N
  else odd_small χ hχ hq (by omega) hodd M N

example : type_of% @pomerance_odd_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_odd_case := rfl

end LeanLab.HelfgottMajor.PVCases1122

#print axioms LeanLab.HelfgottMajor.PVCases1122.interval_le_two_initial
#print axioms LeanLab.HelfgottMajor.PVCases1122.even_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.even_initial
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_small
#print axioms LeanLab.HelfgottMajor.PVCases1122.odd_from_truncated
#print axioms LeanLab.HelfgottMajor.PVCases1122.pomerance_even_case
#print axioms LeanLab.HelfgottMajor.PVCases1122.pomerance_odd_case
