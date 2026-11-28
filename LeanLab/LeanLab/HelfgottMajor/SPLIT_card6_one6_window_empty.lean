import LeanLab.HelfgottMajor.ZeroCount1623

/-!
# Split of the six window leaves of the conductor block `3` to `5`

The leaves `card6_window_empty_three`, `card6_window_empty_four`, `card6_window_empty_five` of
`SPLIT_book_count_band_above_one_mult_le_card_level_le_six.lean` and their twins
`one6_window_empty_three`, `one6_window_empty_four`, `one6_window_empty_five` of
`SPLIT_book_count_band_above_one_mult_le_one_level_le_six.lean` share one statement: for a
primitive `χ` modulo `q ∈ {3, 4, 5}` no strip zero of `L(·, χ)` has imaginary part in
`(1, 2πe / q]`.

Helfgott arXiv 1305.2897v4, section 4.6 page 56, cites D. Platt's thesis: for every primitive
character of conductor `q ≤ 10^5`, all non-trivial zeros of `L(s, χ)` with imaginary part at most
`10^8 / q` lie on the critical line. Since `2πe / q < 10^8 / q`, this puts every zero of the
window on the line `Re s = 1/2`, so the rectangle reduces to a segment:

* LEAF `window_platt_grh_verification`: Platt's GRH verification as quoted on page 56.
* LEAF `window_line_free_three`, `window_line_free_four`, `window_line_free_five`: `L(1/2 + it, χ)`
  has no zero for `1 < t ≤ 2πe / q`. Numerically, burst S2 with mpmath on a grid of 120 points,
  the minimum of `|L(1/2 + it, χ)|` on that segment is about `0.60` for `q = 3`, `0.81` for
  `q = 4`, and `0.55`, `0.63`, `1.04` for the three primitive characters modulo `5`.

Each of the six window leaves is then proved from these leaves, the `_of_leaves` twins below.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-- LEAF: Helfgott arXiv 1305.2897v4 section 4.6 page 56, D. Platt's GRH verification
[Pla11]: for every primitive character `χ` of conductor `q ≤ 10^5`, every non-trivial zero of
`L(s, χ)` with imaginary part at most `10^8 / q` in absolute value has real part exactly `1/2`.
Class HARD: a cited rigorous interval arithmetic computation. WAITING COPY of Platt's thesis,
the statement is read from Helfgott page 56. -/
theorem window_platt_grh_verification (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≤ 10 ^ 5) {ρ : ℂ} (hz : DirichletCharacter.LFunction χ ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hT : |ρ.im| ≤ 10 ^ 8 / (q : ℝ)) : ρ.re = 1 / 2 := by
  sorry

/-- LEAF: the critical segment for the primitive character modulo `3`, the line step of the
window `(1, 2πe / 3]` after Platt's verification, Helfgott section 4.6: `L(1/2 + it, χ) ≠ 0` for
`1 < t ≤ 2πe / 3`. Numerically `|L(1/2 + it, χ₋₃)| ≥ 0.59` there and the first zero is near
`8.04`. Class HARD: a certified evaluation of one `L`-function on a segment. -/
theorem window_line_free_three (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 3)
    {t : ℝ} (ht1 : 1 < t) (ht : t ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ)) :
    DirichletCharacter.LFunction χ (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- LEAF: the critical segment for the primitive character modulo `4`, the line step of the
window `(1, 2πe / 4]` after Platt's verification, Helfgott section 4.6: `L(1/2 + it, χ) ≠ 0` for
`1 < t ≤ 2πe / 4`. Numerically `|L(1/2 + it, χ₋₄)| ≥ 0.81` there and the first zero is near
`6.02`. Class HARD: a certified evaluation of one `L`-function on a segment. -/
theorem window_line_free_four (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 4)
    {t : ℝ} (ht1 : 1 < t) (ht : t ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ)) :
    DirichletCharacter.LFunction χ (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- LEAF: the critical segment for the three primitive characters modulo `5`, the line step of
the window `(1, 2πe / 5]` after Platt's verification, Helfgott section 4.6:
`L(1/2 + it, χ) ≠ 0` for `1 < t ≤ 2πe / 5`. Numerically the minimum of `|L(1/2 + it, χ)|` there
is about `0.55`, `0.63` and `1.04` for the three characters. Class HARD: a certified evaluation
of three `L`-functions on a segment. -/
theorem window_line_free_five (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : q = 5)
    {t : ℝ} (ht1 : 1 < t) (ht : t ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ)) :
    DirichletCharacter.LFunction χ (1 / 2 + t * I) ≠ 0 := by
  sorry

/-- The window height `2πe / q` lies below Platt's height `10^8 / q`. Proved, no input. -/
theorem window_height_le_platt (hq : 0 < q) :
    2 * Real.pi * Real.exp 1 / (q : ℝ) ≤ 10 ^ 8 / (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hp : Real.pi < 4 := Real.pi_lt_four
  apply div_le_div_of_nonneg_right _ hqpos.le
  nlinarith [Real.pi_pos, Real.exp_pos 1]

/-- The common reduction: if Platt's verification puts every window zero on the critical line and
the critical segment `(1, 2πe / q]` carries no zero, the window is empty. Proved from the leaf
`window_platt_grh_verification` and a line hypothesis. -/
theorem window_empty_of_line_free (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≤ 10 ^ 5)
    (hline : ∀ t : ℝ, 1 < t → t ≤ 2 * Real.pi * Real.exp 1 / (q : ℝ) →
      DirichletCharacter.LFunction χ (1 / 2 + t * I) ≠ 0) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, stripZeros, Set.mem_setOf_eq] at hρ
  obtain ⟨⟨hz, h0, h1, hT⟩, -, him⟩ := hρ
  have hre : ρ.re = 1 / 2 :=
    window_platt_grh_verification χ hχ hq hz h0 h1
      (hT.trans (window_height_le_platt (Nat.pos_of_ne_zero (NeZero.ne q))))
  have habs : |ρ.im| = ρ.im := abs_of_pos (by linarith)
  have hρeq : ρ = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  apply hline ρ.im him (habs ▸ hT)
  rw [← hρeq]
  exact hz

/-- Twin of the leaf `card6_window_empty_three`, same statement, proved from the leaves. -/
theorem card6_window_empty_three_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 3) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  window_empty_of_line_free χ hχ (by omega)
    (fun _ ht1 ht => window_line_free_three χ hχ hq ht1 ht)

/-- Twin of the leaf `card6_window_empty_four`, same statement, proved from the leaves. -/
theorem card6_window_empty_four_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 4) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  window_empty_of_line_free χ hχ (by omega)
    (fun _ ht1 ht => window_line_free_four χ hχ hq ht1 ht)

/-- Twin of the leaf `card6_window_empty_five`, same statement, proved from the leaves. -/
theorem card6_window_empty_five_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 5) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  window_empty_of_line_free χ hχ (by omega)
    (fun _ ht1 ht => window_line_free_five χ hχ hq ht1 ht)

/-- Twin of the leaf `one6_window_empty_three`, same statement, proved from the leaves. -/
theorem one6_window_empty_three_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 3) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  card6_window_empty_three_of_leaves χ hχ hq

/-- Twin of the leaf `one6_window_empty_four`, same statement, proved from the leaves. -/
theorem one6_window_empty_four_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 4) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  card6_window_empty_four_of_leaves χ hχ hq

/-- Twin of the leaf `one6_window_empty_five`, same statement, proved from the leaves. -/
theorem one6_window_empty_five_of_leaves (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q = 5) :
    (stripZeros_finite χ (2 * Real.pi * Real.exp 1 / (q : ℝ))).toFinset.filter
      (fun ρ => 0 ≤ ρ.im ∧ 1 < ρ.im) = ∅ :=
  card6_window_empty_five_of_leaves χ hχ hq

end LeanLab.HelfgottMajor.ZeroCount1623
