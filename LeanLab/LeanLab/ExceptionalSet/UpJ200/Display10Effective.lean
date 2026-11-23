import LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelectedDecisions

/-!
# P0082 display 10 by the effective route of Davenport chapter 14, avoiding Siegel

Burst burst-20261122, Claude cloud session S74.

P0082, Brüdern and Perelli 1998, page 358 display 10, left inequality: a real zero `β < 1` of
the L function of a real nonprincipal primitive character modulo `r` satisfies
`1 - β ≫ r^{-1/2} (log r)^{-2}`. The paper cites Davenport, Multiplicative Number Theory,
chapter 14, where the constant is effective. The lab's proof `Task672.landauRealZeroHyp_proved672`
goes through the Siegel bound and so loses effectivity. This file gives the effective route
of Davenport chapter 14 as a split:

* LEAF `leaf_L1_lower`, HARD: `L(1, χ) ≫ r^{-1/2}` with an effective constant, Davenport
  chapter 6, from the class number formula and `h ≥ 1`.
* LEAF `leaf_Lderiv_bound`, MEDIUM: `|L'(σ, χ)| ≪ log² r` for `1 - 1/log r ≤ σ ≤ 1`,
  Davenport chapter 14, partial summation.
* `landauRealZeroHyp_of_leaves`, PROVED sorry free from the two leaves: the exact
  `LandauRealZeroHyp`, by the mean value estimate on `[β, 1]` as in Davenport chapter 14.

Both leaves are effective classical statements, so a proof of them gives display 10 with an
effective constant. AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Display10Effective

open Real Set
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (LandauRealZeroHyp)

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 6, the class number formula with
`h ≥ 1`, as used in chapter 14 for P0082 display 10, class HARD. For a real nonprincipal
primitive character `χ` modulo `r`, `|L(1, χ)| ≥ c r^{-1/2}` with an absolute effective `c > 0`. -/
theorem leaf_L1_lower : ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → c / Real.sqrt r ≤ ‖χ.LFunction 1‖ := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14, the bound
`|L'(σ, χ)| ≪ log² r` for `1 - 1/log r ≤ σ ≤ 1`, by partial summation, as used for P0082
display 10, class MEDIUM. Here `L'(σ, χ)` is the complex derivative of Mathlib's continued
`LFunction` at the real point `σ`. -/
theorem leaf_Lderiv_bound : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 →
      ‖deriv χ.LFunction (σ : ℂ)‖ ≤ C * Real.log r ^ 2 := by
  sorry

/-- P0082 page 358 display 10, left inequality, PROVED sorry free from the two effective
leaves by the argument of Davenport chapter 14: if `β ≤ 1 - 1/log r` the bound is trivial;
otherwise the mean value estimate on `[β, 1]` gives `|L(1, χ)| ≤ (1 - β) max |L'| ≪
(1 - β) log² r`, and `L(1, χ) ≫ r^{-1/2}`. -/
theorem landauRealZeroHyp_of_leaves (H1 : type_of% @leaf_L1_lower)
    (H2 : type_of% @leaf_Lderiv_bound) : LandauRealZeroHyp := by
  obtain ⟨c, hc, h1⟩ := H1
  obtain ⟨C, hC, h2⟩ := H2
  refine ⟨min (1 / 2) (c / C), lt_min (by norm_num) (div_pos hc hC), ?_⟩
  intro r hr χ β hp hreal hχ hβ hz
  have : NeZero r := hr
  have hr2 : 2 ≤ r := by
    have hr0 : r ≠ 0 := NeZero.ne r
    have hr1 : r ≠ 1 := by
      intro heq
      subst r
      exact hχ (DirichletCharacter.level_one χ)
    omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  set L := Real.log (r : ℝ) with hL
  set s := Real.sqrt (r : ℝ) with hs
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hrR
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have hsL : 0 < s * L ^ 2 := by positivity
  set c₃ := min (1 / 2) (c / C) with hc₃
  have hc₃0 : 0 < c₃ := lt_min (by norm_num) (div_pos hc hC)
  rw [div_le_iff₀ hsL]
  by_cases hcase : β ≤ 1 - 1 / L
  · -- the trivial range: `1 - β ≥ 1/log r`
    have hb : 1 / L ≤ 1 - β := by linarith
    have hhalf : c₃ ≤ 1 / 2 := min_le_left _ _
    have hsLge : 1 / 2 ≤ s * L := by nlinarith
    calc c₃ ≤ s * L := le_trans hhalf hsLge
      _ = (1 / L) * (s * L ^ 2) := by field_simp
      _ ≤ (1 - β) * (s * L ^ 2) := mul_le_mul_of_nonneg_right hb hsL.le
  · -- the mean value estimate on `[β, 1]`
    rw [not_le] at hcase
    have hdiff : Differentiable ℂ χ.LFunction := DirichletCharacter.differentiable_LFunction hχ
    have hderiv : ∀ x ∈ Icc β 1, HasDerivWithinAt (fun t : ℝ => χ.LFunction (t : ℂ))
        (deriv χ.LFunction (x : ℂ)) (Icc β 1) x := by
      intro x _
      exact ((hdiff (x : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
    have hbound : ∀ x ∈ Ico β 1, ‖deriv χ.LFunction (x : ℂ)‖ ≤ C * L ^ 2 := by
      intro x hx
      exact h2 r hr χ hp hreal hχ x (by linarith [hx.1]) hx.2.le
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
      ⟨hβ.le, le_refl 1⟩
    have hzero : χ.LFunction ((β : ℝ) : ℂ) = 0 := hz
    simp only [Complex.ofReal_one, hzero, sub_zero] at hmv
    have hlow := h1 r hr χ hp hreal hχ
    -- `c / s ≤ C L² (1 - β)`
    have key : c / s ≤ C * L ^ 2 * (1 - β) := le_trans hlow hmv
    have key2 : c ≤ C * (1 - β) * (s * L ^ 2) := by
      rw [div_le_iff₀ hs0] at key; nlinarith
    have hcC : c₃ ≤ c / C := min_le_right _ _
    calc c₃ ≤ c / C := hcC
      _ ≤ (1 - β) * (s * L ^ 2) := by
          rw [div_le_iff₀ hC]; nlinarith

/-- `LandauRealZeroHyp`, P0082 display 10, CONDITIONAL ON the two effective leaves of
Davenport chapter 14, with no use of the Siegel theorem. -/
theorem landauRealZeroHyp_effective : LandauRealZeroHyp :=
  landauRealZeroHyp_of_leaves leaf_L1_lower leaf_Lderiv_bound

end LeanLab.ExceptionalSet.UpJ200.Display10Effective

#print axioms LeanLab.ExceptionalSet.UpJ200.Display10Effective.landauRealZeroHyp_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Display10Effective.landauRealZeroHyp_effective
