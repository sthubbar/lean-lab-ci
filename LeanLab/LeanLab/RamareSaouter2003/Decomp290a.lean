import LeanLab.RamareSaouter2003.Decomp290c
import LeanLab.RamareSaouter2003.Decomp290b
import LeanLab.RamareSaouter2003.Theorem4LiteralZeta
import LeanLab.RamareSaouter2003.Lemma1Zeta
import LeanLab.RamareSaouter2003.Decomp1531a
import LeanLab.RamareSaouter2003.Decomp1531b

/-!
P0099, Theorem 4, printed pp. 17 to 20, displays 10 to 18.
The explicit formula uses the sign correction in Ramare 2023, Lemma 1.1.
The corrected constant cancels in the psi difference.
AI wrote this Lean code. Binary Goldbach is OPEN.
All six LEAF inputs remain OPEN. The assemblies are CONDITIONAL ON them.
-/

namespace LeanLab.RamareSaouter2003.Decomp290a

open Real Chebyshev Smooth Thm4Parts Thm4Literal Thm4Assembly L3Zeta L3Zeros Decomp290c

/-- LEAF. P0099 p. 16, Lemma 5 proof, citing Montgomery and Vaughan 1973,
Theorem 2. This is only the prime count estimate used for display 10. -/
theorem brun_titchmarsh : MVBrunTitchmarsh := by
  sorry

/-- LEAF. P0099 p. 19, lower half of display 11.
Schoenfeld 1976 p. 356, Theorem 6 star, display 5.4 star. -/
theorem schoenfeld_lower (Z : ℝ) (hZ : 121 ≤ Z) :
    0.998697 * √Z ≤ ψ Z - θ Z := by
  sorry

/-- LEAF. P0099 p. 19, upper half of display 11.
Schoenfeld 1976 p. 356, Theorem 6 star, display 5.3 star. -/
theorem schoenfeld_upper (Z : ℝ) (hZ : 0 < Z) :
    ψ Z - θ Z ≤ 1.001093 * √Z + 3 * Z ^ (1 / 3 : ℝ) := by
  sorry

/-- Display 11 assembled from its separate lower and upper leaves.
CONDITIONAL ON schoenfeld_lower and schoenfeld_upper. -/
theorem schoenfeld : SchoenfeldPT 0.998697 1.001093 :=
  ⟨schoenfeld_lower, schoenfeld_upper⟩

/-- LEAF. P0099 p. 14, verified RH height from Wedeniwski, reference 24.
This finite height input supplies the critical line condition on near zeros. -/
theorem verified_height : RHUpTo 3300000000 := by
  sorry

/-- The weighted identity split into near and far sums. CONDITIONAL ON the
explicit formula and convergence leaves in Decomp290c. -/
theorem weighted_formula (m : ℕ) (X u T : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    (hT : 1000 ≤ T) :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      nearSum m X u T - farSum m X u T -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  have hs := Decomp290c.zero_sum_split m X u T
    (Decomp290c.zeroTerm_summable m X u hm hX hu hmu)
  have hformula := Decomp290c.weighted_formula_total m X u hm hX hu hmu
  linarith

/-- LEAF. P0099 p. 19, the two near zero bounds after display 13, summed
 with multiplicity. Reuse Decomp1531a.near_zero_term_le and the true count.
 This bounds only the near zero contribution in display 15. -/
theorem near_sum_le (hRH : RHUpTo 3300000000) (m : ℕ) (X u T : ℝ)
    (hm : 2 ≤ m) (hX : 10 ^ 12 ≤ X) (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (hT : 1000 ≤ T) (hTT : T ≤ 3300000000) :
    nearSum m X u T ≤ 2 * L1Zeta.NZr T *
      (u * (1 + m * u) * √X * ∫ t in (0 : ℝ)..1, fm m t) := by
  sorry

/-- LEAF. P0099 p. 20, display 14 summed over the far zeros in display 15.
 Reuse Decomp1531a.far_zero_term_le. Lemma 1 supplies summability through
 Lemma 2. This bounds only the far zero contribution. -/
theorem far_sum_le (hN : L1Zeta.Lemma1N) (m : ℕ) (X u T : ℝ)
    (hm : 2 ≤ m) (hX : 10 ^ 12 ≤ X) (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (hT : 1000 ≤ T) :
    farSum m X u T ≤ (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
      (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m * ZsF gZ bZ m T X := by
  sorry

/-- Display 15 from the weighted identity and the two zero sum leaves.
CONDITIONAL ON weighted_formula, near_sum_le and far_sum_le. -/
theorem display15 (hN : L1Zeta.Lemma1N) :
    JLower15Lit L1Zeta.NZr (ZsF gZ bZ) 3300000000 := by
  intro m X u T hm hX hu hmu hT hTT
  apply Decomp1531b.display15_of_split hm hX hu hmu
  · simpa only [Dψ] using weighted_formula m X u T hm hX hu hmu hT
  · exact near_sum_le verified_height m X u T hm hX hu hmu hT hTT
  · exact far_sum_le hN m X u T hm hX hu hmu hT

/-- Theorem 4 assembled from Lemma 1 and the six smaller leaves and the weighted identity.
CONDITIONAL ON those inputs. No sorry occurs in this assembly. -/
theorem theorem4_of_lemma1 (hN : L1Zeta.Lemma1N) : Theorem4Fm L1Zeta.NZr 3300000000 :=
  Thm4LiteralZeta.theorem4Fm_of_zeta_lit brun_titchmarsh schoenfeld (display15 hN)
    verified_height (L1Zeta.lemma1Count_zeta hN)

/-- The exact original target from its new leaves and the Rosser decomposition.
CONDITIONAL ON the twelve OPEN leaves in Decomp290a, Decomp290b and Decomp290c. -/
theorem theorem4_cited : Theorem4Fm L1Zeta.NZr 3300000000 :=
  theorem4_of_lemma1 Decomp290b.lemma1_two_sided

end LeanLab.RamareSaouter2003.Decomp290a

#print axioms LeanLab.RamareSaouter2003.Decomp290a.brun_titchmarsh
#print axioms LeanLab.RamareSaouter2003.Decomp290a.schoenfeld_lower
#print axioms LeanLab.RamareSaouter2003.Decomp290a.schoenfeld_upper
#print axioms LeanLab.RamareSaouter2003.Decomp290a.schoenfeld
#print axioms LeanLab.RamareSaouter2003.Decomp290a.verified_height
#print axioms LeanLab.RamareSaouter2003.Decomp290a.weighted_formula
#print axioms LeanLab.RamareSaouter2003.Decomp290a.near_sum_le
#print axioms LeanLab.RamareSaouter2003.Decomp290a.far_sum_le
#print axioms LeanLab.RamareSaouter2003.Decomp290a.display15
#print axioms LeanLab.RamareSaouter2003.Decomp290a.theorem4_of_lemma1
#print axioms LeanLab.RamareSaouter2003.Decomp290a.theorem4_cited
