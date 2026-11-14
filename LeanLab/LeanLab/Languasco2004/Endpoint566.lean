/-
Jia 1996 pages 271 to 273, affine endpoint control for every remainder term.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Affine566

namespace LeanLab.Languasco2004.RemainderIntegral566
open Real Set RemainderData566
noncomputable section

/-- LEAF. Pages 271 to 273 support: the moving endpoints stay inside their compact rectangle. -/
theorem endpoint_bounds (i : Fin 25) (t : ℝ)
    (htl : (data i 0 : ℝ) ≤ t) (htu : t ≤ (data i 1 : ℝ)) :
    (uMin i : ℝ) ≤ (data i 2 : ℝ) * t + data i 3 ∧
      (data i 2 : ℝ) * t + data i 3 ≤ (uMax i : ℝ) ∧
      (uMin i : ℝ) ≤ (data i 4 : ℝ) * t + data i 5 ∧
      (data i 4 : ℝ) * t + data i 5 ≤ (uMax i : ℝ) ∧
      (data i 2 : ℝ) * t + data i 3 ≤ (data i 4 : ℝ) * t + data i 5 := by
  have hL := Affine566.affine_bounds (data i 2 : ℝ) (data i 3 : ℝ)
    (data i 0 : ℝ) (data i 1 : ℝ) t ⟨htl, htu⟩
  have hU := Affine566.affine_bounds (data i 4 : ℝ) (data i 5 : ℝ)
    (data i 0 : ℝ) (data i 1 : ℝ) t ⟨htl, htu⟩
  obtain ⟨_, _, _, _, hA, hB⟩ := domain_certificate i
  have hAr : (data i 2 : ℝ) * (data i 0 : ℝ) + data i 3 ≤
      (data i 4 : ℝ) * (data i 0 : ℝ) + data i 5 := by exact_mod_cast hA
  have hBr : (data i 2 : ℝ) * (data i 1 : ℝ) + data i 3 ≤
      (data i 4 : ℝ) * (data i 1 : ℝ) + data i 5 := by exact_mod_cast hB
  have hW := Affine566.affine_bounds ((data i 4 : ℝ) - data i 2) ((data i 5 : ℝ) - data i 3)
    (data i 0 : ℝ) (data i 1 : ℝ) t ⟨htl, htu⟩
  have hw0 : 0 ≤ min
      (((data i 4 : ℝ) - data i 2) * (data i 0 : ℝ) + ((data i 5 : ℝ) - data i 3))
      (((data i 4 : ℝ) - data i 2) * (data i 1 : ℝ) + ((data i 5 : ℝ) - data i 3)) :=
    le_min (by nlinarith [hAr]) (by nlinarith [hBr])
  have hw := hw0.trans hW.1
  have hab : (data i 2 : ℝ) * t + data i 3 ≤ (data i 4 : ℝ) * t + data i 5 := by nlinarith
  have hlo : (uMin i : ℝ) ≤ (data i 2 : ℝ) * t + data i 3 := by
    simpa only [uMin, Rat.cast_min, Rat.cast_add, Rat.cast_mul] using hL.1
  have hhi : (data i 4 : ℝ) * t + data i 5 ≤ (uMax i : ℝ) := by
    simpa only [uMax, Rat.cast_max, Rat.cast_add, Rat.cast_mul] using hU.2
  exact ⟨hlo, hab.trans hhi, hlo.trans hab, hhi, hab⟩

#print axioms endpoint_bounds
end
end LeanLab.Languasco2004.RemainderIntegral566
