import LeanLab.Ternary78.Paper104

/-
AI wrote this Lean code. Binary Goldbach is open.
Decomposition of the complete written proof of P0099 Lemma 7 on printed page 22.
-/

namespace LeanLab.Ternary78.Paper104

/-- LEAF. P0099 page 22 Lemma 7, the denominator is positive
in the parameter domain inherited from Theorem 4. -/
theorem lemma7_denominator {m u a : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u)
    (ha : a ≤ 1 / 2) : 1 ≤ 1 + m * u * (1 - a) := by
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  nlinarith

#print axioms lemma7_denominator

/-- LEAF. P0099 page 22 Lemma 7, the first equality in its written proof. -/
theorem lemma7_identity (m u a : ℝ) (hd : 1 + m * u * (1 - a) ≠ 0) :
    1 - (1 + m * u * a) / (1 + m * u * (1 - a)) * Real.exp (-u) =
      (1 + m * u * a) / (1 + m * u * (1 - a)) * (1 - Real.exp (-u)) +
        m * u * (1 - 2 * a) / (1 + m * u * (1 - a)) := by
  field_simp
  ring

#print axioms lemma7_identity

/-- LEAF. P0099 page 22 Lemma 7, the exponential term is at most u. -/
theorem lemma7_exp_term {m u a : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) :
    (1 + m * u * a) / (1 + m * u * (1 - a)) * (1 - Real.exp (-u)) ≤ u := by
  have hmu : 0 ≤ m * u := mul_nonneg hm hu
  have hd : 0 < 1 + m * u * (1 - a) := by nlinarith
  have hr0 : 0 ≤ (1 + m * u * a) / (1 + m * u * (1 - a)) := by positivity
  have hr1 : (1 + m * u * a) / (1 + m * u * (1 - a)) ≤ 1 := by
    apply (div_le_one hd).mpr
    nlinarith
  have he : 1 - Real.exp (-u) ≤ u := by linarith [Real.one_sub_le_exp_neg u]
  calc
    _ ≤ (1 + m * u * a) / (1 + m * u * (1 - a)) * u :=
      mul_le_mul_of_nonneg_left he hr0
    _ ≤ 1 * u := mul_le_mul_of_nonneg_right hr1 hu
    _ = u := one_mul u

#print axioms lemma7_exp_term

/-- LEAF. P0099 page 22 Lemma 7, the second term is bounded
by deleting its denominator, which is at least one. -/
theorem lemma7_gap_term {m u a : ℝ} (hm : 0 ≤ m) (hu : 0 ≤ u)
    (ha : a ≤ 1 / 2) :
    m * u * (1 - 2 * a) / (1 + m * u * (1 - a)) ≤ m * u * (1 - 2 * a) := by
  apply div_le_self
  · exact mul_nonneg (mul_nonneg hm hu) (by linarith)
  · exact lemma7_denominator hm hu ha

#print axioms lemma7_gap_term

/-- The exact cited Lemma7 Prop, assembled from its paper proof leaves. -/
theorem lemma7_decomposed : Lemma7 := by
  intro m hm u a hu ha0 ha
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [lemma7_identity (m : ℝ) u a (by linarith [lemma7_denominator hm0 hu ha])]
  calc
    _ ≤ u + m * u * (1 - 2 * a) :=
      add_le_add (lemma7_exp_term hm0 hu ha0 ha) (lemma7_gap_term hm0 hu ha)
    _ = u * (1 + (1 - 2 * a) * m) := by ring

#print axioms lemma7_decomposed

end LeanLab.Ternary78.Paper104
