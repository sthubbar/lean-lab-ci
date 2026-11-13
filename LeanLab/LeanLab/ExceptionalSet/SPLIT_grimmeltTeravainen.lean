/-
Split of `grimmeltTeravainen` of `LeanLab.ExceptionalSet.ChenPrimes` into the two cases of the
proof of Theorem 1.1, in the window form of the theorem that the lab already reduces it to.

`GT11` is `∃ δ > 0, ∃ C, ∀ N ≥ 1, EChen N ≤ C * N ^ (1 - δ)`, where `EChen N` counts the `m ≤ N`
with `m ≡ 4 mod 6` that are not a sum of two Chen primes. The lab's route to `GT11` sorts `[1, X]`
into windows `[5N/4, 7N/4]`: a power saving on the exceptions in every window gives a power saving
on `EChen` (`cntI`, `ChenBad`, `WindowBound`, `powerBound_of_windowBound`, `echen_eq_cnt` and
`gt11_of_intervalBound`, all proved in `LeanLab.ExceptionalSet.GrimmeltTeravainen2025Sorting`,
whose `IntervalBound` is `WindowBound ChenBad`). Nothing here redoes that step and nothing here
uses `grimmeltTeravainen`.

What is left is the count in one window, and the source proves it in two cases, on pages 67 and 69:
the unexceptional case, where no Dirichlet character of modulus at most `N ^ (2 * δ₁ ^ 3)` has a
real zero above `1 - (1 / 2) / log (N ^ (2 * δ₁ ^ 3))` (Definition 7.1, at quality `1 / 2`), and
the exceptional case, where one does. The two leaves
`window_count_unexceptional_case` and `window_count_exceptional_case` of
`LeanLab.ExceptionalSet.SPLIT_grimmeltTeravainen_cases` are exactly those two cases of the
window count, each under its own case hypothesis; this module only states them, under the names
`window_count_unexceptional` and `window_count_exceptional`, and proves each of the two from its
leaf. Each leaf asks only for a bound with a logarithmic
loss and for the saving `δ₁ ^ 6`, weaker than the saving `(δ₁ / 10) ^ 4` proved on page 67 because
`δ₁ ^ 2 < 10 ^ (-4)` on the range `0 < δ₁ < 1 / 200` of the two leaves, so each leaf is strictly
easier than the window bound it feeds, and neither of them is `GT11`.

The assembly `grimmeltTeravainen_split` is the classical case analysis on the exceptional zero,
with the two constants combined, the logarithmic loss turned into a power saving, and the result
sorted into `[1, N]`. It is admission free and it does not use `grimmeltTeravainen`.

Both leaves are OPEN and live in `SPLIT_grimmeltTeravainen_cases`, each carrying its own LEAF
comment. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.ChenPrimes
import LeanLab.ExceptionalSet.GrimmeltTeravainen2025Sorting
import LeanLab.ExceptionalSet.SPLIT_grimmeltTeravainen_cases

open Finset
open LeanLab.AlmostPrimes

namespace LeanLab.ExceptionalSet

open LeanLab.ExceptionalSet.GT2025

attribute [local instance] Classical.propDecidable

/-- The unexceptional case of the window count, page 67 of P0039: no exceptional zero
below the quality `1 / 2` at modulus `N ^ (2 * δ₁ ^ 3)`. Stated here under the name the assembly
uses; its content, Lemma 8.3 with the upper bound sieve, is the leaf
`window_count_unexceptional_case` of `LeanLab.ExceptionalSet.SPLIT_grimmeltTeravainen_cases`, and
this declaration is that leaf by name. -/
theorem window_count_unexceptional :
    ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 / 200 → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ¬ (∃ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (β : ℝ),
          3 ≤ r + 1 ∧ (r + 1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁ ^ 3) ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧
            β < 1 ∧ 1 - (1 / 2) / Real.log ((N : ℝ) ^ (2 * δ₁ ^ 3)) ≤ β ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0) →
        (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ₁ ^ 6) * Real.log (N : ℝ) := window_count_unexceptional_case

/-- The exceptional case of the window count, page 69 of P0039: an exceptional zero
below the quality `1 / 2` at modulus `N ^ (2 * δ₁ ^ 3)` exists. Stated here under the name the
assembly uses; its content, Lemma 8.4 with the partition by `σ₁(m)` at `-1 / 2`, is the leaf
`window_count_exceptional_case` of `LeanLab.ExceptionalSet.SPLIT_grimmeltTeravainen_cases`, and
this declaration is that leaf by name. -/
theorem window_count_exceptional :
    ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 / 200 → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∃ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (β : ℝ),
          3 ≤ r + 1 ∧ (r + 1 : ℝ) ≤ (N : ℝ) ^ (2 * δ₁ ^ 3) ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧
            β < 1 ∧ 1 - (1 / 2) / Real.log ((N : ℝ) ^ (2 * δ₁ ^ 3)) ≤ β ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0) →
        (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - δ₁ ^ 6) * Real.log (N : ℝ) := window_count_exceptional_case

/-- ASSEMBLY. `GT11`, from the two cases of the window count. At `δ₁ = 1 / 1000` and at each `N`
exactly one of the two case hypotheses of the leaves holds, so the larger of the two constants and
the saving `η = δ₁ ^ 6` bound the count with the logarithmic loss; then
`log N ≤ N ^ (η / 2) / (η / 2)` spends the loss and leaves the power saving `η / 2`, which is
`WindowBound ChenBad`. The module's sorting step `gt11_of_intervalBound` carries that window bound
to `GT11`. No step uses `grimmeltTeravainen`. -/
theorem grimmeltTeravainen_split : GT11 := by
  have hδ : (0 : ℝ) < 1 / 1000 := by norm_num
  have hδ' : (1 / 1000 : ℝ) < 1 / 200 := by norm_num
  obtain ⟨C₁, hC₁, N₁, h1⟩ := window_count_unexceptional (1 / 1000) hδ hδ'
  obtain ⟨C₂, hC₂, N₂, h2⟩ := window_count_exceptional (1 / 1000) hδ hδ'
  set η : ℝ := (1 / 1000 : ℝ) ^ 6 with hη
  have hη0 : 0 < η := by rw [hη]; norm_num
  have hhalf : (0 : ℝ) < η / 2 := by linarith
  have hCmax : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
  refine gt11_of_intervalBound ?_
  show WindowBound ChenBad
  refine ⟨η / 2, hhalf, max C₁ C₂ / (η / 2), max (max N₁ N₂) 1, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNa : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hN1
  have hpow0 : 0 ≤ (N : ℝ) ^ (1 - η) := (Real.rpow_pos_of_pos hNr _).le
  have hlog : Real.log (N : ℝ) ≤ (N : ℝ) ^ (η / 2) / (η / 2) :=
    Real.log_le_rpow_div (le_of_lt hNr) hhalf
  -- the two cases give one window count with the logarithmic loss
  have hb : (cntI ChenBad N : ℝ) ≤ max C₁ C₂ * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ)) := by
    have step : ∀ C : ℝ, C ≤ max C₁ C₂ →
        (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - η) * Real.log (N : ℝ) →
        (cntI ChenBad N : ℝ) ≤ max C₁ C₂ * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ)) := by
      intro C hC hbC
      have hX : 0 ≤ (N : ℝ) ^ (1 - η) * Real.log (N : ℝ) := mul_nonneg hpow0 hlog0
      calc (cntI ChenBad N : ℝ) ≤ C * (N : ℝ) ^ (1 - η) * Real.log (N : ℝ) := hbC
        _ = C * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ)) := by ring
        _ ≤ max C₁ C₂ * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hC hX
    by_cases hE : (∃ (r : ℕ) (χ : DirichletCharacter ℂ (r + 1)) (β : ℝ),
        3 ≤ r + 1 ∧ (r + 1 : ℝ) ≤ (N : ℝ) ^ (2 * (1 / 1000 : ℝ) ^ 3) ∧ χ.IsPrimitive ∧
          χ ≠ 1 ∧ β < 1 ∧
            1 - (1 / 2) / Real.log ((N : ℝ) ^ (2 * (1 / 1000 : ℝ) ^ 3)) ≤ β ∧
              DirichletCharacter.LFunction χ (β : ℂ) = 0)
    · exact step C₂ (le_max_right _ _) (h2 N hNb hE)
    · exact step C₁ (le_max_left _ _) (h1 N hNa hE)
  -- the logarithmic loss is spent on a smaller power
  have hb2 : max C₁ C₂ * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ))
      ≤ max C₁ C₂ / (η / 2) * (N : ℝ) ^ (1 - η / 2) := by
    have hstep1 : (N : ℝ) ^ (1 - η) * Real.log (N : ℝ)
        ≤ (N : ℝ) ^ (1 - η) * ((N : ℝ) ^ (η / 2) / (η / 2)) :=
      mul_le_mul_of_nonneg_left hlog hpow0
    have hstep2 : (N : ℝ) ^ (1 - η) * ((N : ℝ) ^ (η / 2) / (η / 2))
        = ((N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η / 2)) / (η / 2) := by ring
    have hstep3 : (N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η / 2) = (N : ℝ) ^ (1 - η / 2) := by
      have hexp : 1 - η + η / 2 = 1 - η / 2 := by ring
      rw [← Real.rpow_add hNr, hexp]
    calc max C₁ C₂ * ((N : ℝ) ^ (1 - η) * Real.log (N : ℝ))
        ≤ max C₁ C₂ * ((N : ℝ) ^ (1 - η) * ((N : ℝ) ^ (η / 2) / (η / 2))) :=
          mul_le_mul_of_nonneg_left hstep1 hCmax
      _ = max C₁ C₂ * (((N : ℝ) ^ (1 - η) * (N : ℝ) ^ (η / 2)) / (η / 2)) := by rw [hstep2]
      _ = max C₁ C₂ * ((N : ℝ) ^ (1 - η / 2) / (η / 2)) := by rw [hstep3]
      _ = max C₁ C₂ / (η / 2) * (N : ℝ) ^ (1 - η / 2) := by ring
  exact le_trans hb hb2

-- Axiom audit driver for the assembly.
#print axioms grimmeltTeravainen_split

end LeanLab.ExceptionalSet
