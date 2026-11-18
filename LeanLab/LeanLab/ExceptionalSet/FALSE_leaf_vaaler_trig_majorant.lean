/-
The leaf `leaf_vaaler_trig_majorant` of `ExceptionalSet/SPLIT_leaf_fejer_majorant.lean` is FALSE.

That leaf asks, for every `H` and every `0 ≤ z₂ < z₁ ≤ 1`, for a trigonometric polynomial
`θ ↦ (z₁ - z₂) + ∑ h ∈ Icc 1 H, (c h * e(hθ)).re` that stays within `2/(H+1)` of the indicator of
`z₂ ≤ {θ} < z₁` at EVERY real point `θ`.  A trigonometric polynomial is continuous, while the
indicator jumps by `1` at `θ = z₁` when `z₁ < 1`, and at `θ = z₂` when `0 < z₂`.  A continuous
function cannot stay within `r < 1/2` of a function with a jump of size `1`: on the two sides of
the jump the triangle inequality would give `1 ≤ 2r + ε` for every `ε > 0`.  Since
`2/(H+1) < 1/2` when `H ≥ 4`, the leaf fails for every `H ≥ 4` and every interval other
than the full one `z₂ = 0`, `z₁ = 1`.  The cases `H ≤ 3` are not decided here.

Consequence: `leaf_fejer_majorant_split` in the split file calls this leaf, so that assembly rests
on a false statement.  The parent `leaf_fejer_majorant` is not shown false by this file.

Remark, not a Lean result: what Vaaler's lemma gives is a pointwise bound by a nonnegative Fejer-type kernel
`K(θ - z₁) + K(θ - z₂)`, large near the endpoints and of mean `O(1/(H+1))`; it does not give a
uniform bound.  This is standard mathematics, the Gibbs obstruction at a jump.

Results, all fully proved, nothing admitted:
* `not_uniform_approx_of_jump`      the continuity obstruction, in general form;
* `not_vaaler_of_lt_one`            no such `c` when `4 ≤ H` and `z₁ < 1`;
* `not_vaaler_of_pos`               no such `c` when `4 ≤ H` and `0 < z₂`;
* `leaf_vaaler_trig_majorant_false` the negation of the statement of the leaf, verbatim.

The statement of the leaf itself is not changed and this file does not use it.
AI wrote this Lean code.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_fejer_majorant

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- A continuous `g` cannot stay within `r < 1/2` of a function `f` that has a jump of size `1`
at `x`, that is, takes values at distance `1` from `f x` arbitrarily close to `x`. -/
theorem not_uniform_approx_of_jump (f g : ℝ → ℝ) (hg : Continuous g) (x r : ℝ) (hr : r < 1 / 2)
    (hjump : ∀ δ > 0, ∃ y, |y - x| < δ ∧ |f y - f x| = 1) :
    ¬ ∀ θ, |f θ - g θ| ≤ r := by
  intro h
  have hε : (0 : ℝ) < 1 - 2 * r := by linarith
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.mp hg x (1 - 2 * r) hε
  obtain ⟨y, hy, hy1⟩ := hjump δ hδ
  have h1 : |g y - g x| < 1 - 2 * r := by
    have := hδg y (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  have h2 := h y
  have h3 := h x
  have h4 : |f y - f x| ≤ |f y - g y| + |g y - g x| + |f x - g x| := by
    have e : f y - f x = (f y - g y) + (g y - g x) - (f x - g x) := by ring
    rw [e]
    have a1 := abs_sub ((f y - g y) + (g y - g x)) (f x - g x)
    have a2 := abs_add_le (f y - g y) (g y - g x)
    linarith
  linarith

/-- The trigonometric polynomial of the leaf, with its constant term, is continuous. -/
theorem continuous_trig_poly (H : ℕ) (b : ℝ) (c : ℕ → ℂ) :
    Continuous (fun θ : ℝ => b + ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re) := by
  unfold eC
  fun_prop

/-- For `H ≥ 4` the uniform bound `2/(H+1)` of the leaf is below `1/2`. -/
theorem two_div_lt_half (H : ℕ) (hH : 4 ≤ H) : 2 / ((H : ℝ) + 1) < 1 / 2 := by
  have h4 : (4 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- No trigonometric polynomial does what the leaf asks when `H ≥ 4` and `z₁ < 1`: the indicator
jumps from `1` to `0` at `θ = z₁`. -/
theorem not_vaaler_of_lt_one (H : ℕ) (hH : 4 ≤ H) (z₁ z₂ : ℝ) (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁)
    (hz₁ : z₁ < 1) :
    ¬ ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
        - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1) := by
  rintro ⟨c, -, hc⟩
  refine not_uniform_approx_of_jump
    (fun θ : ℝ => if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0)
    (fun θ : ℝ => (z₁ - z₂) + ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re)
    (continuous_trig_poly H (z₁ - z₂) c) z₁ (2 / ((H : ℝ) + 1)) (two_div_lt_half H hH) ?_ ?_
  · intro δ hδ
    refine ⟨max z₂ (z₁ - δ / 2), ?_, ?_⟩
    · have hle : max z₂ (z₁ - δ / 2) < z₁ := max_lt hz1 (by linarith)
      have hge : z₁ - δ / 2 ≤ max z₂ (z₁ - δ / 2) := le_max_right _ _
      rw [abs_lt]
      constructor <;> linarith
    · have hy1 : max z₂ (z₁ - δ / 2) < z₁ := max_lt hz1 (by linarith)
      have hy2 : z₂ ≤ max z₂ (z₁ - δ / 2) := le_max_left _ _
      have hfy : Int.fract (max z₂ (z₁ - δ / 2)) = max z₂ (z₁ - δ / 2) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      have hfz : Int.fract z₁ = z₁ := Int.fract_eq_self.mpr ⟨by linarith, hz₁⟩
      simp only [hfy, hfz]
      rw [if_pos ⟨hy2, hy1⟩, if_neg (fun hh => lt_irrefl _ hh.2)]
      norm_num
  · intro θ
    have := hc θ
    rwa [sub_sub] at this

/-- No trigonometric polynomial does what the leaf asks when `H ≥ 4` and `0 < z₂`: the indicator
jumps from `0` to `1` at `θ = z₂`. -/
theorem not_vaaler_of_pos (H : ℕ) (hH : 4 ≤ H) (z₁ z₂ : ℝ) (hz₂ : 0 < z₂) (hz1 : z₂ < z₁)
    (hz₁ : z₁ ≤ 1) :
    ¬ ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
      ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
        - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1) := by
  rintro ⟨c, -, hc⟩
  refine not_uniform_approx_of_jump
    (fun θ : ℝ => if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0)
    (fun θ : ℝ => (z₁ - z₂) + ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re)
    (continuous_trig_poly H (z₁ - z₂) c) z₂ (2 / ((H : ℝ) + 1)) (two_div_lt_half H hH) ?_ ?_
  · intro δ hδ
    refine ⟨max 0 (z₂ - δ / 2), ?_, ?_⟩
    · have hle : max 0 (z₂ - δ / 2) < z₂ := max_lt hz₂ (by linarith)
      have hge : z₂ - δ / 2 ≤ max 0 (z₂ - δ / 2) := le_max_right _ _
      rw [abs_lt]
      constructor <;> linarith
    · have hy1 : max 0 (z₂ - δ / 2) < z₂ := max_lt hz₂ (by linarith)
      have hy2 : (0 : ℝ) ≤ max 0 (z₂ - δ / 2) := le_max_left _ _
      have hfy : Int.fract (max 0 (z₂ - δ / 2)) = max 0 (z₂ - δ / 2) :=
        Int.fract_eq_self.mpr ⟨hy2, by linarith⟩
      have hfz : Int.fract z₂ = z₂ := Int.fract_eq_self.mpr ⟨hz₂.le, by linarith⟩
      simp only [hfy, hfz]
      rw [if_neg (fun hh => absurd hh.1 (not_le.mpr hy1)), if_pos ⟨le_refl _, hz1⟩]
      norm_num
  · intro θ
    have := hc θ
    rwa [sub_sub] at this

/-- The statement of `leaf_vaaler_trig_majorant` is false.  The negated proposition is that
statement verbatim.  Witness: `H = 4`, `z₂ = 0`, `z₁ = 1/2`, where the bound `2/5` is below half
of the jump of the indicator at `θ = 1/2`. -/
theorem leaf_vaaler_trig_majorant_false :
    ¬ ∀ (H : ℕ) (z₁ z₂ : ℝ) (_ : 0 ≤ z₂) (_ : z₂ < z₁) (_ : z₁ ≤ 1),
      ∃ c : ℕ → ℂ, (∀ h ∈ Finset.Icc 1 H, ‖c h‖ ≤ 2 / ((h : ℝ) + 1)) ∧
        ∀ θ : ℝ, |(if z₂ ≤ Int.fract θ ∧ Int.fract θ < z₁ then (1 : ℝ) else 0) - (z₁ - z₂)
          - ∑ h ∈ Finset.Icc 1 H, (c h * eC (h * θ)).re| ≤ 2 / ((H : ℝ) + 1) := by
  intro h
  exact not_vaaler_of_lt_one 4 le_rfl (1 / 2) 0 le_rfl (by norm_num) (by norm_num)
    (h 4 (1 / 2) 0 le_rfl (by norm_num) (by norm_num))

/-- The same fact stated against the type of the leaf itself, so that no transcription of the
statement is involved: any proof of a proposition equal to the leaf's yields `False`. -/
theorem leaf_vaaler_trig_majorant_type_false
    (h : type_of% @leaf_vaaler_trig_majorant) : False :=
  leaf_vaaler_trig_majorant_false h

end LeanLab.ExceptionalSet.U1539
