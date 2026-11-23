import Mathlib
import LeanLab.PNTPort.BV.PolyaVinogradov
import LeanLab.HelfgottMajor.PolyaVinogradov123

/-!
Route burst S58, burst-20261122, tag pv420-split.
Split of the CITED-LEFT leaf `PolyaVinogradov123.polya_vinogradov_4_20`, P0014 page 36
display 4.20, which Helfgott cites from Pomerance 2011, Remarks on the Polya-Vinogradov
inequality, Integers 11A, Article 19, Theorem 1.

Source situation. The Integers PDF returned 403 and the de Gruyter copy is paywalled; arXiv
1009.5779 is an unrelated physics paper. Pomerance's talk slides pvtalk.pdf, slide 13, state the
theorem with no proof. Frolenkov, arXiv 1107.0381, Section 3 and Section 5, quotes Pomerance's
ingredients: Lemma 3 of [Pomerance], the bound for the sum of |sin jx|/j; the bound of
[Pomerance, Section 4] for the sum of |cos mα - cos mβ|/m; and [Pomerance, display 10], the
Gauss sum identity split by parity; together with |τ(χ)| = √q. The split below follows those
quoted displays. Pomerance's S(χ) is the maximum over all M, N of the norm of the sum of χ(a)
for M ≤ a ≤ M + N, per slide 8, so initial segments are the special case M = 1.

Proved here, from Mathlib and the lab's PNTPort files: the Gauss sum identity in exponential
form, its even and odd forms which are Pomerance display 10, |τ(χ)| = √q, and the assembly.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PV420Split1122

open Real Finset

/-- Pomerance display 10 in exponential form, as quoted by Frolenkov display 14:
for χ primitive, `χ⁻¹(n) τ(χ) = ∑_x χ(x) e(n x / q)`. PROVED from Mathlib's
`gaussSum_mulShift_of_isPrimitive`. -/
theorem gauss_twist {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (n : ZMod q) :
    χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x * ZMod.stdAddChar (n * x) := by
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ, gaussSum]
  rfl

/-- Frolenkov display 13, used by Pomerance: `|τ(χ)| = √q` for χ primitive. PROVED. -/
theorem norm_gauss {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q := by
  rw [← LeanLab.PNTPort.LargeSieve.normSq_gaussSum_of_isPrimitive hχ,
    Real.sqrt_sq (norm_nonneg _)]

/-- Reflection used for Pomerance display 10: `∑_x χ(x) e(n x/q) = χ(-1) ∑_x χ(x) e(-n x/q)`.
PROVED. -/
theorem sum_reflect {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    ∑ x : ZMod q, χ x * ZMod.stdAddChar (n * x) =
      χ (-1) * ∑ x : ZMod q, χ x * ZMod.stdAddChar (-(n * x)) := by
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  rw [mul_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, mul_neg, neg_neg]
  have hx : χ (-x) = χ (-1) * χ x := by rw [← map_mul, neg_one_mul]
  rw [hx]
  linear_combination (-(χ x * ZMod.stdAddChar (n * x))) * hsq

/-- Pomerance display 10, even case, as quoted by Frolenkov display 14 with χ⁻¹ in place of χ:
for χ primitive and even, `χ⁻¹(n) τ(χ) = ∑_x χ(x) cos(2π n x/q)`, the cosine written as
`(e(nx/q) + e(-nx/q))/2`. PROVED. -/
theorem gauss_twist_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (heven : χ (-1) = 1) (n : ZMod q) :
    χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) + ZMod.stdAddChar (-(n * x))) / 2) := by
  have h1 := gauss_twist hχ n
  have h2 := sum_reflect χ n
  rw [heven, one_mul] at h2
  simp only [mul_div_assoc', mul_add, add_div, sum_add_distrib, ← sum_div]
  rw [← h2, ← h1]; ring

/-- Pomerance display 10, odd case, as quoted by Frolenkov display 14 with χ⁻¹ in place of χ:
for χ primitive and odd, `χ⁻¹(n) τ(χ) = i ∑_x χ(x) sin(2π n x/q)`, the term `i sin` written as
`(e(nx/q) - e(-nx/q))/2`. PROVED. -/
theorem gauss_twist_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hodd : χ (-1) ≠ 1) (n : ZMod q) :
    χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2) := by
  have hm : χ (-1) = -1 := by
    have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hodd
    · exact eq_neg_of_add_eq_zero_left h
  have h1 := gauss_twist hχ n
  have h2 := sum_reflect χ n
  rw [hm] at h2
  simp only [mul_div_assoc', mul_sub, sub_div, sum_sub_distrib, ← sum_div]
  have : ∑ x : ZMod q, χ x * ZMod.stdAddChar (-(n * x)) =
      -∑ x : ZMod q, χ x * ZMod.stdAddChar (n * x) := by rw [h2]; ring
  rw [this, ← h1]; ring

/-- LEAF: Pomerance 2011 Lemma 3, quoted as Lemma 1 of Frolenkov arXiv 1107.0381:
for all real x and positive integers n, the sum over 1 ≤ j ≤ n of |sin jx|/j is below
2/π log n + 2/π times γ + log 2 + 3/n. Class MEDIUM. -/
theorem pomerance_lemma3 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n) := by
  sorry

/-- LEAF: Pomerance 2011 Section 4, quoted as Lemma 2 of Frolenkov arXiv 1107.0381:
for all real α, β and positive integers n, the sum over 1 ≤ m ≤ n of |cos mα - cos mβ|/m is
below log n + γ + log 2 + 3/n. Class MEDIUM. -/
theorem pomerance_sec4 (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n := by
  sorry

/-- LEAF: Pomerance 2011, proof of Theorem 1 for even χ: the Polya Fourier expansion of the
interval indicator with explicit truncation error, Frolenkov display 12 style, reduced through
display 10 and |τ(χ)| = √q to the sum of |sin|/j, bounded by Lemma 3, then the choice of the
truncation parameter. The quoted inputs are hypotheses. Conclusion: Pomerance's S(χ) bound for
χ(-1) = 1, all intervals M ≤ a ≤ N. Class HARD. -/
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
  sorry

/-- LEAF: Pomerance 2011, proof of Theorem 1 for odd χ: the same Polya Fourier expansion with
explicit truncation error, reduced through display 10 and |τ(χ)| = √q to the sum of
|cos mα - cos mβ|/m, bounded by Section 4, then the choice of the truncation parameter.
The quoted inputs are hypotheses. Conclusion: Pomerance's S(χ) bound for χ(-1) ≠ 1, all
intervals M ≤ a ≤ N. Class HARD. -/
theorem pomerance_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  sorry

/-- Assembly: exactly the sealed statement `PolyaVinogradov123.polya_vinogradov_4_20`, from the
LEAFs and the two proved Gauss sum facts. Initial segments are the intervals with M = 1. -/
theorem polya_vinogradov_4_20 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  refine ciSup_le fun n => ?_
  split_ifs with h
  · exact pomerance_even_case χ hχ hq pomerance_lemma3 (gauss_twist_even hχ h) (norm_gauss hχ) h 1 n
  · exact pomerance_odd_case χ hχ hq pomerance_sec4 (gauss_twist_odd hχ h) (norm_gauss hχ) h 1 n

example : type_of% @polya_vinogradov_4_20 =
    type_of% @LeanLab.HelfgottMajor.PolyaVinogradov123.polya_vinogradov_4_20 := rfl

end LeanLab.HelfgottMajor.PV420Split1122

#print axioms LeanLab.HelfgottMajor.PV420Split1122.gauss_twist
#print axioms LeanLab.HelfgottMajor.PV420Split1122.norm_gauss
#print axioms LeanLab.HelfgottMajor.PV420Split1122.sum_reflect
#print axioms LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even
#print axioms LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_odd
#print axioms LeanLab.HelfgottMajor.PV420Split1122.polya_vinogradov_4_20
