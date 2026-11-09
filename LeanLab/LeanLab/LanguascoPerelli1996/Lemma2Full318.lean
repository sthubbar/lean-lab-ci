import LeanLab.LanguascoPerelli1996.Decomp108

/-!
P0071 pages 354 and 355, Lemma 2 with the existing amended large height range.
The original declaration header and historical doc comment are retained.
Its former cited status is superseded by the complete proof below.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996

/-- CITED. Lemma 2, Section 3, p. 354, with `T ≥ 1`. A conditional assembly is
`Decomp108.lemma2_of_decomposed`, CONDITIONAL ON `Decomp108.variation_control`. -/
theorem lemma2 : Lemma2 := by
  exact Decomp108.lemma2_of_decomposed


end LeanLab.LanguascoPerelli1996

#print axioms LeanLab.LanguascoPerelli1996.lemma2
