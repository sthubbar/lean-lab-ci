import LeanLab.RamareSaouter2003.Decomp290c

/-!
P0099 p. 19, the finite near part after display 13.
The lab already proves rectangle finiteness in ExplicitPsi1.Residues.
This file bridges that result to the multiplicity index and finite support.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359a

open Complex L3Zeta LeanLab.PNTPort.ExplicitPsi1 Set

/-- LEAF. P0099 p. 19 after display 13.
For each height the actual zero indices in the closed ordinate band are finite.
This is the compact rectangle argument already proved in the lab. -/
theorem ordinate_band_finite (T : ℝ) : {i : ZI | |gZ i| ≤ T}.Finite := by
  have hS : {ρ : Zall | (ρ : ℂ) ∈
      Rectangle ⟨-1 / 2, -|T|⟩ ⟨1, |T|⟩ ∩ riemannZetaZeros}.Finite :=
    (zeros_rect_finite 1 |T|).preimage Subtype.val_injective.injOn
  have hsig := hS.sigma (t := fun ρ : Zall =>
    (univ : Set (Fin (analyticOrderNatAt riemannZeta (ρ : ℂ)))))
    (fun _ _ => Set.toFinite _)
  apply hsig.subset
  rintro ⟨ρ, k⟩ hi
  refine ⟨?_, mem_univ _⟩
  obtain ⟨hz, hr0, hr1⟩ := mem_strip ρ
  simp only [mem_ofPred_eq]
  refine ⟨(mem_rect (by norm_num) (abs_nonneg T)).mpr
    ⟨⟨by linarith, hr1.le⟩, ?_⟩, hz⟩
  have hab : |(ρ : ℂ).im| ≤ |T| := hi.trans (le_abs_self T)
  exact abs_le.mp hab

/-- The exact near_support_finite target of Decomp290c.
P0099 p. 19 after display 13. The support is a subset of a finite band. -/
theorem near_support_finite (m : ℕ) (X u : ℝ) :
    (Function.support (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then
      Decomp290c.zeroTerm m X u i else 0)).Finite := by
  apply (ordinate_band_finite 1000).subset
  intro i hi
  by_contra h
  change ¬ |gZ i| ≤ (1000 : ℝ) at h
  simp [Function.mem_support, h] at hi

end LeanLab.RamareSaouter2003.Decomp359a

#print axioms LeanLab.RamareSaouter2003.Decomp359a.ordinate_band_finite
#print axioms LeanLab.RamareSaouter2003.Decomp359a.near_support_finite
