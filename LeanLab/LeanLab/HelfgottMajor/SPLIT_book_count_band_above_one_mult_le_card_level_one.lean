import LeanLab.HelfgottMajor.SPLIT_book_count_band_above_one_mult_le_card

/-!
# Split of `book_count_band_above_one_mult_le_card_level_one`

AI wrote this Lean code. Binary Goldbach is open.

The level one leaf is about the Dirichlet `L`-function of the unique character of modulus `1`.
Mathlib identifies that `L`-function with `riemannZeta`, `DirichletCharacter.LFunction_modOne_eq`.
The split separates that bridging, proved here, from the published zero data of `ζ`, stated as
one leaf in its own form: `ζ` has at most one zero `ρ` with `0 < Re ρ < 1` and
`1 < Im ρ ≤ 2πe ≈ 17.08`. The first two ordinates are `14.1347…` and `21.0220…`, so this is
true; it is the classical computation of the first zeros, Gram 1903, Backlund 1914.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

/-- LEAF: zero data of ζ below height 2πe, the published first zeros. HARD, a certified count of
the zeros of ζ up to height 18, by the argument principle with interval arithmetic.
CITED: Gram 1903 and Backlund 1914, first zeros of ζ; Odlyzko's zero tables; LMFDB L-function
1-1-1.1-r0-0-0, ordinates 14.134725… and 21.022039…. In this form: the nontrivial zeros of ζ
with ordinate in `(1, 2πe]`, `2πe < 17.08`, form a set with at most one element. -/
theorem zeta_strip_zeros_above_one_le_two_pi_e_subsingleton :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 1 < ρ.im ∧
      ρ.im ≤ 2 * Real.pi * Real.exp 1}.Subsingleton := by
  sorry

/-- Bridging, proved: for modulus `1` a strip zero of `L(·, χ)` in the window above height `1`
up to `2πe` is a nontrivial zero of `ζ` with ordinate in `(1, 2πe]`. -/
lemma level_one_window_mem_zeta_set (χ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ (stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)) :
    ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 1 < ρ.im ∧
      ρ.im ≤ 2 * Real.pi * Real.exp 1} := by
  have hp := Finset.mem_filter.mp hρ
  have hz := (stripZeros_finite χ _).mem_toFinset.mp hp.1
  obtain ⟨hL, hre0, hre1, him⟩ := hz
  rw [DirichletCharacter.LFunction_modOne_eq] at hL
  exact ⟨hL, hre0, hre1, hp.2.2, (le_abs_self _).trans him⟩

/-- `book_count_band_above_one_mult_le_card_level_one`, with exactly its statement, from the
ζ leaf and the proved bridging through `LFunction_modOne_eq`. -/
theorem book_count_band_above_one_mult_le_card_level_one_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q = 1) :
    ((stripZeros_finite χ (2 * Real.pi * Real.exp 1)).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im)).card ≤ 1 := by
  subst hq
  rw [Finset.card_le_one]
  intro a ha b hb
  exact zeta_strip_zeros_above_one_le_two_pi_e_subsingleton
    (level_one_window_mem_zeta_set χ ha) (level_one_window_mem_zeta_set χ hb)

end LeanLab.HelfgottMajor.ZeroCount1623
