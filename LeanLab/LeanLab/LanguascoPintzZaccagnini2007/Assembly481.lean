import LeanLab.LanguascoPintzZaccagnini2007.Decomp481c

/-!
Supply assembly for the sealed printed Corollary 4.2 on J of X.
The original cor42_published131 and Cor42OnWindow131 stay unchanged.
This is CONDITIONAL on the cited and open leaves in Decomp481a through c.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

/-- P0045 page 6, Corollary 4.2. The exact sealed target assembled from the new leaves.
This assembly remains CONDITIONAL on those leaves. -/
theorem cor42_published131_of_leaves : Cor42OnWindow131 evenJ131 := by
  intro η hη
  obtain ⟨K₁, Cstar, A, H, T, hC, hA, hH, hT, Xf, hf⟩ :=
    explicit_formula_reduction481 pintz_explicit_formula481 jutila_density481
      indexed_zero_count481 gamma_pair_bound481 η hη
  obtain ⟨c, hc, Xr, hr⟩ := exceptional_radical481 davenport_classification481
    real_zero_bound481 iwaniec_zero_free481 H T hH hT
  refine ⟨K₁, Cstar, c, A, hC, hc, hA, max Xf Xr, ?_⟩
  intro X hX
  obtain ⟨P, E, hP, hcard, hsource, hgood, hall⟩ :=
    hf X ((le_max_left _ _).trans hX)
  refine ⟨P, E, hP, ⟨hcard, ?_⟩, hgood, hall⟩
  intro r hmem
  obtain ⟨z, hz, hzr⟩ := hsource r hmem
  simpa only [hzr] using hr X ((le_max_right _ _).trans hX) P hP z hz

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.cor42_published131_of_leaves
