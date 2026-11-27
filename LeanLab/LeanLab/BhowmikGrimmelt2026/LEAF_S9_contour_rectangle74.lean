/-
Repaired contour step for Lemma 7.4 of P0029, display 7.12 on page 27.

The sealed leaf `leaf_contour_shift74` of `SPLIT_lemma74.lean` is suspected false as
stated: it omits the part of the line `re s = 2` above height `T` and it adds the two
horizontal pieces where the residue theorem subtracts them, see the note
notes/burst-20261124/BhowmikGrimmelt2026-S9-23-contour-shift74.md.  This file states
the standard rectangle identity in its correct form, as a new LEAF for a later route.
It does not change and does not prove the sealed leaf.  The corrected identity is
proved here from the two leaves of `LEAF_S9_rectangle_parts74.lean` and the proved
right line formula `arithmetic_right_line469`.

AI wrote the Lean code.  Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_lemma74
import LeanLab.BhowmikGrimmelt2026.LEAF_S9_rectangle_parts74

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- LEAF: P0029 page 27, display 7.12, the contour shift step of the standard proof,
corrected. Class HARD.

For a primitive `χ`, a smooth compactly supported kernel `Ψ` supported in `Ioi S` with
`1 ≤ S`, `0 < B`, `0 < T`, and no zero of the L-function on the boundary of the
rectangle with corners `-B ± iT` and `2 ± iT`, the arithmetic side minus the pole term
at `s = 1`, plus the zeros inside the rectangle counted with analytic multiplicity,
equals the shifted vertical line at `re s = -B`, plus `1 / (2 π i)` times the top
horizontal piece minus the bottom one, plus the part of the line `re s = 2` with
`|Im s| > T`.  This is Cauchy's residue theorem on the rectangle together with the
Mellin inversion of the arithmetic side along `re s = 2`. -/
theorem leaf_contour_rectangle74 (B T : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (S : ℝ) (Ψ : ℝ → ℝ) (hB : 0 < B) (hT : 0 < T)
    (hS : 1 ≤ S) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
    (hχ : χ.IsPrimitive)
    (hvert : ∀ t : ℝ, |t| ≤ T →
      DirichletCharacter.LFunction χ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hhor : ∀ σ : ℝ, -B ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - (T : ℂ) * Complex.I) ≠ 0) :
    ∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T},
        (mult χ ρ : ℂ) * mellinR Ψ ρ) =
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ),
        ((-(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) *
            mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) -
          (-(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) *
            mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I))) +
      (1 / (2 * Real.pi)) * (∫ t in {t : ℝ | T < |t|},
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hS0 : 0 < S := by linarith
  have hline := arithmetic_right_line469 Ψ S hS0 hsm hcs hsupp r χ 2 (by norm_num)
  have hsplit := leaf_right_line_split74 T hT r χ S Ψ hS hsm hcs hsupp
  have hres := leaf_rectangle_residue74 B T r χ S Ψ hB hT hS hsm hcs hsupp hχ hvert hhor
  rw [hline, hsplit]
  push_cast at hres ⊢
  simp only [Pi.neg_apply] at hres ⊢
  linear_combination hres

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_contour_rectangle74
