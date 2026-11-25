import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_one
import LeanLab.HelfgottMajor.Feed1122ZetaAboveFourOne

/-!
# Split of `book_count_band_above_one_mult_le_one_level_one`

AI wrote this Lean code. Binary Goldbach is open.

The level one leaf is about the Dirichlet `L`-function of the unique character of modulus `1`.
Mathlib identifies that `L`-function with `riemannZeta`, `DirichletCharacter.LFunction_modOne_eq`,
so the multiplicity `mult χ ρ` is the analytic order of `ζ` at `ρ`. The split separates that
bridging, proved here, from the published fact in its own form: every nontrivial zero of `ζ`
with ordinate in `(1, 2πe]`, `2πe ≈ 17.08`, is simple. The only such zero is `1/2 + 14.1347… i`,
and its simplicity is part of every rigorous verification of the first zeros.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

/-- Split burst S126 at height `4` in `Feed1122ZetaAboveFourOne`, was a LEAF: simplicity of the zeros of ζ below height 2πe, the published first zero. HARD, a
certified computation that `ζ'` does not vanish at the zero `1/2 + 14.1347… i`, together with
the certified count that it is the only zero of ordinate in `(1, 2πe]`.
CITED: Platt and Trudgian, The Riemann hypothesis is true up to 3·10^12, Bull. LMS 53, 2021,
all zeros up to that height are simple; also Gram 1903, Backlund 1914, LMFDB L-function
1-1-1.1-r0-0-0. In this form: every nontrivial zero of ζ with ordinate in `(1, 2πe]` has
analytic order at most one. -/
theorem zeta_strip_zero_above_one_le_two_pi_e_order_le_one :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → 1 < ρ.im →
      ρ.im ≤ 2 * Real.pi * Real.exp 1 → (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ 1 := by
  exact LeanLab.HelfgottMajor.Feed1122ZetaAboveFourOne.zeta_strip_zero_above_one_le_two_pi_e_order_le_one_split

/-- Bridging, proved: for modulus `1` the multiplicity of a zero of `L(·, χ)` is the analytic
order of `ζ` there, by `LFunction_modOne_eq`. -/
lemma level_one_mult_eq_zeta_order (χ : DirichletCharacter ℂ 1) (ρ : ℂ) :
    mult χ ρ = analyticOrderNatAt riemannZeta ρ := by
  show analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = _
  rw [DirichletCharacter.LFunction_modOne_eq]

/-- `book_count_band_above_one_mult_le_one_level_one`, with exactly its statement, from the
ζ leaf and the proved bridging through `LFunction_modOne_eq`. -/
theorem book_count_band_above_one_mult_le_one_level_one_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ∀ ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im), (mult χ ρ : ℝ) ≤ 1 := by
  subst hq
  intro ρ hρ
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ _).mem_toFinset.mp hp.1
  obtain ⟨hL, hre0, hre1, him⟩ := hz
  rw [DirichletCharacter.LFunction_modOne_eq] at hL
  rw [level_one_mult_eq_zeta_order]
  exact zeta_strip_zero_above_one_le_two_pi_e_order_le_one ρ hL hre0 hre1 hp.2.2
    ((le_abs_self _).trans him)

end LeanLab.HelfgottMajor.ZeroCount1623
