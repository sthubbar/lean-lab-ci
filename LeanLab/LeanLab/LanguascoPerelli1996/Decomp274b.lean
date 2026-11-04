import LeanLab.LanguascoPerelli1996.Decomp274a

/-!
P0071 Lemma 2, pages 354 and 355. Reuse the leaves in Decomp274a.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp274b
open Real

/-- Pages 354 and 355, Lemma 2 assembled from the new leaves and the
proved endpoint control. Exactly the sealed Lemma2 statement.
CONDITIONAL ON band_variation_cauchy_schwarz and band_derivative_mass. -/
theorem lemma2_decomposed : Lemma2 := by
  intro hGRH
  obtain ⟨A, hA, he⟩ := Decomp108.endpoint_control hGRH
  obtain ⟨B, hB, hv⟩ := Decomp274a.variation_control_decomposed hGRH
  refine ⟨Real.sqrt (A * (2 + B)), ?_⟩
  intro X hX U T hU hUT hT q inst a ha M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM U le_rfl hUT.le)
  apply Decomp108.square_to_rpow (by positivity) (le_trans (by norm_num) hT) hM0
  exact Decomp108.large_height_square hA hT hM0 (hM T hUT.le le_rfl)
    (hM U le_rfl hUT.le) (he X hX U T hU hUT q a ha)
    (hv X hX U T hU hUT hT q a ha M hM)


end LeanLab.LanguascoPerelli1996.Decomp274b

#print axioms LeanLab.LanguascoPerelli1996.Decomp274b.lemma2_decomposed
