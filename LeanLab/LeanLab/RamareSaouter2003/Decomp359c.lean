import LeanLab.RamareSaouter2003.Decomp290c
import LeanLab.RamareSaouter2003.Decomp1531a

/-!
P0099 p. 20, display 14 and the far part of display 15.
The pointwise integration estimate is already proved in Decomp1531a.
The remaining bridge removes X to beta by the critical strip bound.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359c

open Real Smooth L3Zeta Decomp290c

/-- LEAF. P0099 p. 20, display 14 used in display 15.
The proved per-zero estimate bounds the far norm with X in place of
X to beta since every nontrivial zero is in the critical strip. -/
theorem far_pointwise_bound (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (i : ZI) (hi : (1000 : ℝ) < |gZ i|) :
    ‖zeroTerm m X u i‖ ≤
      ((Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
        (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m) * X *
          (1 / |gZ i| ^ (m + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hδ : 0 < (m : ℝ) * u := mul_pos hm0 hu
  have hX0 : 0 < X := by linarith
  obtain ⟨hb0, hb1⟩ := bZ_mem i
  have hγ : ((i.1 : ℂ)).im ≠ 0 := by
    change gZ i ≠ 0
    intro hh
    norm_num [hh] at hi
  have h := Decomp1531a.far_zero_term_le hb0 hb1 hγ hu.le hδ hX0 m
  have hpow : X ^ ((i.1 : ℂ)).re ≤ X := by
    calc _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb1
         _ = X := Real.rpow_one X
  have hmu : 0 ≤ muStar m := by
    unfold muStar
    exact div_nonneg
      (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _))
      (Decomp1531a.integral_fm_pos m).le
  have hK : 0 ≤ (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
      (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m := by
    have := (Decomp1531a.integral_fm_pos m).le
    positivity
  change ‖zeroTerm m X u i‖ ≤ _ at h
  calc _ ≤ _ := h
       _ ≤ _ := by
         have hg : 0 ≤ |gZ i| ^ (m + 1) := by positivity
         have hd := div_le_div_of_nonneg_right hpow hg
         have hh := mul_le_mul_of_nonneg_left hd hK
         convert hh using 1 <;> dsimp [gZ] <;> ring

/-- The exact far_norm_majorant target of Decomp290c.
P0099 p. 20, displays 14 and 15. The constant is explicit and nonnegative. -/
theorem far_norm_majorant (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ZI,
      ‖if (1000 : ℝ) < |gZ i| then zeroTerm m X u i else 0‖ ≤
        C * (if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0) := by
  have hmu0 : 0 ≤ muStar m := by
    unfold muStar
    exact div_nonneg
      (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _))
      (Decomp1531a.integral_fm_pos m).le
  refine ⟨((Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
      (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m) * X, ?_, ?_⟩
  · have := (Decomp1531a.integral_fm_pos m).le
    have : 0 ≤ X := by linarith
    positivity
  · intro i
    by_cases hi : (1000 : ℝ) < |gZ i|
    · simpa only [if_pos hi] using far_pointwise_bound m X u hm hX hu i hi
    · simp only [if_neg hi, norm_zero, mul_zero, le_refl]

end LeanLab.RamareSaouter2003.Decomp359c

#print axioms LeanLab.RamareSaouter2003.Decomp359c.far_pointwise_bound
#print axioms LeanLab.RamareSaouter2003.Decomp359c.far_norm_majorant
