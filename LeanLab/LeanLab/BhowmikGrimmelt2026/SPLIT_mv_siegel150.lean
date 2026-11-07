/-
A split of the Siegel zero case of Theorem 5.1 into four leaves, plus an assembly that
combines them. The leaves are (1) the range of the Gallagher estimate at the dyadic point
`N = ⌊X⌋₊` with `R = X ^ ϑ`, (2) the weighted bound that follows from the Proposition 5.2
input, (3) the step from that weighted bound to the dyadic exceptional count, where the
uniform lower bound including proper prime powers is used, and (4) the absorption of the
factor `1 - β` and its logarithm into `1 / ϑ`.
AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150b

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerSaving)
open ArithmeticFunction

/-- LEAF. Step 1, the range: for a fixed `ϑ` below one fifth the point `N = ⌊X⌋₊` with
`R = X ^ ϑ` is inside the range where the Gallagher estimate is available, both logarithms
are positive and both nodes are at least two, once `X` is large enough. -/
theorem siegel_range150 (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      2 ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ∧
      Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ X ^ ϑ ∧
      X ^ ϑ ≤ (⌊X⌋₊ : ℝ) ∧
      (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) ∧ 2 ≤ X ∧
      0 < Real.log X ∧ 0 < Real.log (X ^ ϑ) := by
  sorry

/-- LEAF. Step 2, the weighted bound: part two of the Proposition 5.2 input, specialised to
`N = ⌊X⌋₊` and `R = X ^ ϑ`, with the factor `1 - β` and its logarithm retained, and only the
range of step 1 assumed. The decidable instances are written out because the source file
makes them local instances. -/
theorem siegel_upper150 (h52 : Prop52) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (X ϑ : ℝ), 2 ≤ X → 0 < ϑ → ϑ < 1 / 5 →
        2 ≤ Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) →
        Real.exp (Real.sqrt (Real.log ⌊X⌋₊)) ≤ X ^ ϑ →
        X ^ ϑ ≤ (⌊X⌋₊ : ℝ) →
        ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
          SiegelZero (X ^ ϑ) r₀ χ₀ β →
          primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
            C * (1 - β) * Real.log ⌊X⌋₊ *
              Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := by
  sorry

/-- LEAF. Step 3, the count from the weighted bound: each even `N` in `[X/2, X]` which fails
to be a sum of two primes contributes at least a fixed multiple of `log X / X` to the
weighted sum of step 2, uniformly in the Siegel data. This is where the uniform lower bound
for the main term, proper prime powers included, is used. -/
theorem siegel_count150 (hGallagher : GallagherStandard) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X ϑ : ℝ), 2 ≤ X → 0 < ϑ → ϑ < 1 / 5 →
        ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
          SiegelZero (X ^ ϑ) r₀ χ₀ β →
          (Edy X : ℝ) ≤ C * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) := by
  sorry

/-- LEAF. Step 4, the scalar absorption: the factor `1 - β` against its own logarithm is at
most `1 / ϑ`, since a Siegel zero at level `X ^ ϑ` gives `1 - β ≤ 1 / log (X ^ ϑ)` and
`log ⌊X⌋₊ ≤ log X`. -/
theorem siegel_absorb150 (X ϑ β : ℝ) (hϑ : 0 < ϑ) (hϑ5 : ϑ < 1 / 5) (hX : 2 ≤ X)
    (hβlow : 1 - 1 / Real.log (X ^ ϑ) < β) (hβlt : β < 1) :
    (1 - β) * Real.log ⌊X⌋₊ ≤ 1 / ϑ := by
  sorry

/-- The Siegel zero case of Theorem 5.1, assembled from the four leaves above. -/
theorem mv_siegel150_split (h52 : Prop52) (hGallagher : GallagherStandard) :
    ∃ ϑ₀ : ℝ, 0 < ϑ₀ ∧ ∀ ϑ : ℝ, 0 < ϑ → ϑ < ϑ₀ → ϑ < 1 / 5 →
      ∃ C X₀ : ℝ, ∀ X : ℝ, 2 ≤ X → X₀ ≤ X →
        (∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
          SiegelZero (X ^ ϑ) r χ β) →
        (Edy X : ℝ) ≤ C * X ^ (1 - ϑ / 2) := by
  obtain ⟨c, C₂, hc, hC₂, hP⟩ := siegel_upper150 h52
  obtain ⟨C₁, hC₁, hcount⟩ := siegel_count150 hGallagher
  refine ⟨1 / 5, by norm_num, ?_⟩
  intro ϑ hϑ _hϑlt hϑ5
  obtain ⟨Xr, hXr⟩ := siegel_range150 ϑ hϑ hϑ5
  refine ⟨C₁ * C₂ / ϑ, Xr, ?_⟩
  intro X hX2 hX hsig
  obtain ⟨r₀, hr₀, χ₀, β, hS⟩ := hsig
  haveI : NeZero r₀ := hr₀
  obtain ⟨h1, h2, h3, hN2, _hX2', hlogX, hlogR⟩ := hXr X hX
  have hSc := hS
  obtain ⟨-, -, -, hβlow, hβlt, -⟩ := hSc
  have hXpos : 0 < X := by linarith
  have hlogNnn : 0 ≤ Real.log ⌊X⌋₊ := by
    have hle : Real.log 2 ≤ Real.log ⌊X⌋₊ := Real.log_le_log (by norm_num) hN2
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have h1βnn : 0 ≤ 1 - β := by linarith
  have hE0 : -(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ) ≤ 0 := by
    have hpos : 0 ≤ (c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ) :=
      div_nonneg (by positivity) (le_of_lt hlogR)
    have hneg : -(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)
        = -((c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) := neg_div _ _
    rw [hneg]
    linarith
  have hexp1 : Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hE0
  have hub :
      primSum (X ^ ϑ)         (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
              (fun n => (vonMangoldt n : ℂ) * χ n -
                  @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                  (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
      C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) :=
    hP X ϑ hX2 hϑ hϑ5 h1 h2 h3 r₀ χ₀ β hS
  have hbr :
      (Edy X : ℝ) ≤ C₁ * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) :=
    hcount X ϑ hX2 hϑ hϑ5 r₀ χ₀ β hS
  have hmul :
      C₁ * primSum (X ^ ϑ)           (fun r _ χ => intervalMax ⌊X⌋₊ (X ^ ϑ)
                (fun n => (vonMangoldt n : ℂ) * χ n -
                    @ite ℂ (χ = 1) (Classical.propDecidable (χ = 1)) 1 0 +
                  @ite ℂ (r = r₀ ∧ HEq χ χ₀)
                    (Classical.propDecidable (r = r₀ ∧ HEq χ χ₀)) ((n : ℂ) ^ ((β : ℂ) - 1)) 0)) ≤
      C₁ * (C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))) :=
    mul_le_mul_of_nonneg_left hub (le_of_lt hC₁)
  have hscalar :
      C₂ * (1 - β) * Real.log ⌊X⌋₊ *
        Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤ C₂ * (1 / ϑ) := by
    have hstep :
        C₂ * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ)) ≤
        C₂ * (1 - β) * Real.log ⌊X⌋₊ * 1 := by
      refine mul_le_mul_of_nonneg_left hexp1 ?_
      exact mul_nonneg (mul_nonneg (le_of_lt hC₂) h1βnn) hlogNnn
    have hβ : (1 - β) * Real.log ⌊X⌋₊ ≤ 1 / ϑ :=
      siegel_absorb150 X ϑ β hϑ hϑ5 hX2 hβlow hβlt
    have hβ' : C₂ * ((1 - β) * Real.log ⌊X⌋₊) ≤ C₂ * (1 / ϑ) :=
      mul_le_mul_of_nonneg_left hβ (le_of_lt hC₂)
    calc C₂ * (1 - β) * Real.log ⌊X⌋₊ *
          Real.exp (-(c * Real.log ⌊X⌋₊) / Real.log (X ^ ϑ))
        ≤ C₂ * (1 - β) * Real.log ⌊X⌋₊ * 1 := hstep
      _ = C₂ * ((1 - β) * Real.log ⌊X⌋₊) := by ring
      _ ≤ C₂ * (1 / ϑ) := hβ'
  refine (hbr.trans (hmul.trans
    (mul_le_mul_of_nonneg_left hscalar (le_of_lt hC₁)))).trans ?_
  have hone : (1 : ℝ) ≤ X ^ (1 - ϑ / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hnn : (0 : ℝ) ≤ C₁ * (C₂ * (1 / ϑ)) := by
    have h2 : (0 : ℝ) < C₂ * (1 / ϑ) := mul_pos hC₂ (one_div_pos.mpr hϑ)
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt h2)
  calc C₁ * (C₂ * (1 / ϑ)) ≤ C₁ * (C₂ * (1 / ϑ)) * X ^ (1 - ϑ / 2) :=
        le_mul_of_one_le_right hnn hone
    _ = C₁ * C₂ / ϑ * X ^ (1 - ϑ / 2) := by ring

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.mv_siegel150_split
