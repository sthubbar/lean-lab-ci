import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-!
# Theorem 6.3 in Pintz's form: the PROPOSED REPAIR for the thm63 QUESTION

AI wrote this file. Binary Goldbach is OPEN.

This file does NOT change `Theorem63` of `Statements.lean`. It records the QUESTION raised on
branch `claude/BhowmikGrimmelt2026-thm63`: P0029 page 24, Theorem 6.3, display 6.8, fixes the
major-arc cut-off at `R = X ^ ϑ`, while the cited source, Pintz Theorem A, P0016 page 4,
display 2.10, only gives SOME cut-off `P` in the open interval `(X ^ (ϑ - ε), X ^ ϑ)`, for
`0 < ε < ε₀`, chosen after the even number `m`, and the conductor bound of the exceptional set
display 2.7 and the arcs of display 2.3 both use that `P`.

* `MajorArcEstimateIn Pset ε₀` is the estimate of display 6.8 with the cut-off `P` existentially
  chosen from the set `Pset ε ϑ X`, for `ε < ε₀`. All quantifiers other than the choice of `P`
  and the bound `ε < ε₀` are exactly those of `Theorem63`.
* `Theorem63PintzForm` is the proposed repair: `P ∈ (X ^ (ϑ - ε), X ^ ϑ)` and some `ε₀ > 0`, as
  in Pintz Theorem A.
* `theorem63_iff_fixed` PROVES that `Theorem63` is exactly the special case `Pset = {X ^ ϑ}`,
  with the vacuous bound `ε₀ = 1`; so the gap between `Theorem63` and Pintz is exactly the choice
  of `P` and the bound `ε₀`.
* `theorem63_closed` and `theorem63Closed_of_pintz` PROVE that both forms imply the common
  weakening with `P ∈ (X ^ (ϑ - ε), X ^ ϑ]`.

The one LEAF is Pintz Theorem A, display 2.10, transported to the normalisation `EM` of P0029
display 5.1 page 19, as P0029 page 24 display 6.8 records it. No finer split was found: the local
steps on P0029 pages 23 and 24, displays 6.2 to 6.7 and 6.9, concern the set `𝓔`, the series
`𝔖(χ₁, χ₂, N)` and the beta factor, not the passage from display 2.10 to display 6.8, which P0029
makes without a display.
-/

/-- The major-arc estimate of P0029 display 6.8, page 24, with the cut-off `P` of `EM` and of
`calEZ` chosen in `Pset ε ϑ X` after `N`, as in Pintz Theorem A, P0016 page 4, display 2.10, and
with `ε < ε₀`. The arcs are those of display 5.1, page 19, the set `𝓔` that of display 6.2,
page 23, the series `𝔖` that of display 6.4, page 23. Every other quantifier is the one of
`Theorem63`. -/
def MajorArcEstimateIn (Pset : ℝ → ℝ → ℝ → Set ℝ) (ε₀ : ℝ) : Prop :=
  ∀ ε ϑ : ℝ, 0 < ε → ε < ε₀ → ε < ϑ → ϑ < 4 / 9 - ε → ∃ c C : ℝ, 0 < c ∧
    ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N →
      X / 2 ≤ N → (N : ℝ) ≤ X → ∃ P ∈ Pset ε ϑ X,
      ‖EM N P - ∑ᶠ (p : (ℂ × PChar) × (ℂ × PChar))
          (_ : p.1 ∈ calEZ H T P X ∧ p.2 ∈ calEZ H T P X),
          genSing p.1.2.2 p.2.2.2 N * betaC p.1.1 p.2.1 * (N : ℂ) ^ (p.1.1 + p.2.1 - 1)‖ ≤
        C * (X * Real.exp (-c * H) + X / Real.sqrt T + X ^ (1 - ε))

/-- PROPOSED REPAIR of `Theorem63`, not a change to it: Theorem 6.3 of P0029, display 6.8,
page 24, in the form of its cited source, Pintz Theorem A, P0016 page 4, display 2.10: there is
`ε₀ > 0` such that for `0 < ε < ε₀`, `ε < ϑ < 4/9 - ε`, and every even `N ∈ [X/2, X]` there is
`P ∈ (X ^ (ϑ - ε), X ^ ϑ)` with the estimate at cut-off `P`. -/
def Theorem63PintzForm : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    MajorArcEstimateIn (fun ε ϑ X => Set.Ioo (X ^ (ϑ - ε)) (X ^ ϑ)) ε₀

/-- The common weakening of `Theorem63` and `Theorem63PintzForm`: the cut-off may also be the
top end point, `P ∈ (X ^ (ϑ - ε), X ^ ϑ]`. -/
def Theorem63Closed : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    MajorArcEstimateIn (fun ε ϑ X => Set.Ioc (X ^ (ϑ - ε)) (X ^ ϑ)) ε₀

/-- LEAF: Pintz Theorem A, P0016 page 4, display 2.10, as cited by P0029 page 24, display 6.8,
Theorem 6.3, and transported to the normalisation `EM` of P0029 display 5.1, page 19, with the
exceptional set of P0029 display 6.2, page 23, at Pintz's cut-off `P`, display 2.7. HARD: this is
the whole explicit formula of Pintz part I, Theorem 1 and Main Lemma 1. Cited, not proved here. -/
theorem leaf_pintz_thmA_display_2_10 : Theorem63PintzForm := by
  sorry

/-- `MajorArcEstimateIn` is monotone: a larger set of allowed cut-offs and a smaller `ε₀` give a
weaker statement. PROVED. -/
theorem MajorArcEstimateIn.mono {Pset Pset' : ℝ → ℝ → ℝ → Set ℝ} {ε₀ ε₀' : ℝ}
    (hP : ∀ ε ϑ X, 0 < ε → 1 < X → Pset ε ϑ X ⊆ Pset' ε ϑ X) (hε : ε₀' ≤ ε₀)
    (h : MajorArcEstimateIn Pset ε₀) : MajorArcEstimateIn Pset' ε₀' := by
  intro ε ϑ hε0 hεε hεϑ hϑ
  obtain ⟨c, C, hc, hrest⟩ := h ε ϑ hε0 (lt_of_lt_of_le hεε hε) hεϑ hϑ
  refine ⟨c, C, hc, fun H T hH hT => ?_⟩
  obtain ⟨X₀, hX⟩ := hrest H T hH hT
  refine ⟨max X₀ 2, fun X hX₀ N hN h1 h2 => ?_⟩
  obtain ⟨P, hPmem, hPest⟩ := hX X (le_trans (le_max_left _ _) hX₀) N hN h1 h2
  exact ⟨P, hP ε ϑ X hε0 (by linarith [le_max_right X₀ 2]) hPmem, hPest⟩

/-- BRIDGE, PROVED: `Theorem63` is exactly the special case of the Pintz-shaped estimate with the
cut-off forced to `P = X ^ ϑ`; the bound `ε < 1` is vacuous since `ε < ϑ < 4/9 - ε`. So the
difference between `Theorem63` and `Theorem63PintzForm` is exactly the choice of `P`, together
with Pintz's bound `ε < ε₀`. -/
theorem theorem63_iff_fixed :
    Theorem63 ↔ MajorArcEstimateIn (fun _ ϑ X => {X ^ ϑ}) 1 := by
  constructor
  · intro h ε ϑ hε _ hεϑ hϑ
    obtain ⟨c, C, hc, hrest⟩ := h ε ϑ hε hεϑ hϑ
    refine ⟨c, C, hc, fun H T hH hT => ?_⟩
    obtain ⟨X₀, hX⟩ := hrest H T hH hT
    exact ⟨X₀, fun X hX₀ N hN h1 h2 => ⟨X ^ ϑ, rfl, hX X hX₀ N hN h1 h2⟩⟩
  · intro h ε ϑ hε hεϑ hϑ
    obtain ⟨c, C, hc, hrest⟩ := h ε ϑ hε (by linarith) hεϑ hϑ
    refine ⟨c, C, hc, fun H T hH hT => ?_⟩
    obtain ⟨X₀, hX⟩ := hrest H T hH hT
    refine ⟨X₀, fun X hX₀ N hN h1 h2 => ?_⟩
    obtain ⟨P, hPmem, hPest⟩ := hX X hX₀ N hN h1 h2
    rw [Set.mem_singleton_iff] at hPmem
    subst hPmem
    exact hPest

/-- PROVED: `Theorem63` implies the common weakening `Theorem63Closed`, since `X ^ ϑ` lies in
`(X ^ (ϑ - ε), X ^ ϑ]` once `X > 1`. -/
theorem theorem63_closed (h : Theorem63) : Theorem63Closed := by
  refine ⟨1, one_pos, ?_⟩
  refine MajorArcEstimateIn.mono (Pset := fun _ ϑ X => {X ^ ϑ}) (ε₀ := 1) ?_ le_rfl
    (theorem63_iff_fixed.mp h)
  intro ε ϑ X hε hX P hP
  rw [Set.mem_singleton_iff] at hP
  subst hP
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hX (by linarith), le_rfl⟩

/-- PROVED: Pintz's form implies the common weakening `Theorem63Closed`. -/
theorem theorem63Closed_of_pintz (h : Theorem63PintzForm) : Theorem63Closed := by
  obtain ⟨ε₀, hε₀, hest⟩ := h
  exact ⟨ε₀, hε₀, hest.mono (fun _ _ _ _ _ => Set.Ioo_subset_Ioc_self) le_rfl⟩

/-- ASSEMBLY, no sorry in its own proof: the common weakening `Theorem63Closed` from the one
LEAF, Pintz Theorem A display 2.10. CONDITIONAL ON `leaf_pintz_thmA_display_2_10`. -/
theorem theorem63Closed_from_leaf : Theorem63Closed :=
  theorem63Closed_of_pintz leaf_pintz_thmA_display_2_10

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.MajorArcEstimateIn.mono
#print axioms LeanLab.BhowmikGrimmelt2026.theorem63_iff_fixed
#print axioms LeanLab.BhowmikGrimmelt2026.theorem63_closed
#print axioms LeanLab.BhowmikGrimmelt2026.theorem63Closed_of_pintz
#print axioms LeanLab.BhowmikGrimmelt2026.theorem63Closed_from_leaf
