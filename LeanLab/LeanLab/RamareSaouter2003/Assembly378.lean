import LeanLab.RamareSaouter2003.Assembly359
import LeanLab.RamareSaouter2003.Decomp378a
import LeanLab.RamareSaouter2003.Decomp378b
import LeanLab.RamareSaouter2003.Decomp378c
import LeanLab.RamareSaouter2003.Decomp378d

/-!
P0099 pp. 14 to 20, the refreshed exact-target assemblies.
The new convergence and subtraction proofs replace the old OPEN snapshots.
The contour estimate and external inputs remain CONDITIONAL.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Assembly378
open Real Chebyshev Smooth Thm4Assembly L3Zeta L3Zeros Thm4Literal Decomp290c Row1

/-- P0099 p. 19 before display 13, exactly the existing weighted_formula_total target.
The existing proved Task259 formula applies at both scales. -/
theorem weighted_formula_total (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      (∑' i : ZI, zeroTerm m X u i).re -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  exact Decomp378d.weighted_formula_total m X u hm hX hu hmu

/-- P0099 p. 19, exactly the weighted explicit formula split at T.
The existing proved Task259 formula applies at both scales. -/
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
  have hs := Decomp290c.zero_sum_split m X u T (Decomp378b.zeroTerm_summable m X u hm hX hu hmu)
  have hf := weighted_formula_total m X u hm hX hu hmu
  linarith

/-- Rosser 1941 pp. 223 and 224, exactly the existing high_count target.
CONDITIONAL ON the cutoff transition, powered count inequality and new circle leaf. -/
theorem high_count (T : ℝ) (hT : 1400 ≤ T) :
    |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  obtain ⟨A, hA, hFA, hbase⟩ := Decomp359g.cutoff_transition
  by_cases hTA : T ≤ A
  · have h := hbase T hT hTA
    have hlog : 6.9074 ≤ Real.log T := VerifyU1333.log_thousand_ge.trans
      (Real.log_le_log (by norm_num) (by linarith : (1000 : ℝ) ≤ T))
    have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
    linarith
  · obtain ⟨k, hk, hcount⟩ := Decomp359g.powered_jensen_count A T hA hFA (le_of_lt (lt_of_not_ge hTA))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN, hkN, hG, hJ⟩ := Decomp378c.powered_jensen_estimate A T hA hFA
      (le_of_lt (lt_of_not_ge hTA)) k (ε / 2) hk (by positivity)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hkdiv : k / (N : ℝ) ≤ ε / 2 := (div_le_iff₀ hNR).mpr (by nlinarith)
    have hc := hcount N hN hG
    linarith

/-- P0099 p. 14, the two-sided true count bound.
CONDITIONAL ON the Rosser source leaves and unchanged low_count citation. -/
theorem lemma1_two_sided : L1Zeta.Lemma1N := by
  intro T hT
  by_cases h : T ≤ 1400
  · have hR := Decomp290b.low_count T hT h
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1000) hT
    have hlow := VerifyU1333.log_thousand_ge
    have hpi := VerifyU1333.log_two_pi_le
    have hbound : (2 : ℝ) ≤ 0.67 * Real.log (T / (2 * π)) := by
      rw [Real.log_div (by linarith : T ≠ 0) (by positivity : 2 * π ≠ 0)]
      linarith
    exact hR.trans hbound
  · have hR := high_count T (by linarith)
    have hE := VerifyU1333.rosser_err_le T hT
    have hpos : 0 ≤ (0.2 : ℝ) / T := div_nonneg (by norm_num) (by linarith)
    linarith

/-- P0099 p. 14, exactly the original upper-count input.
CONDITIONAL ON the Rosser source leaves and unchanged low_count citation. -/
theorem lemma1_cited : Lemma1Upper L1Zeta.NZr := by
  intro T hT
  have h := lemma1_two_sided T hT
  have hab := le_abs_self (L1Zeta.NZr T -
    (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8))
  linarith

/-- P0099 p. 20, display 15 on the actual zero family.
CONDITIONAL ON the explicit actual count premise and the unchanged finite-height RH citation. -/
theorem display15 (hN : L1Zeta.Lemma1N) :
    JLower15Lit L1Zeta.NZr (ZsF gZ bZ) 3300000000 := by
  intro m X u T hm hX hu hmu hT hTT
  apply Decomp1531b.display15_of_split (Near := nearSum m X u T) (Far := farSum m X u T) hm hX hu hmu
  · change (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) = _
    have hs := Decomp290c.zero_sum_split m X u T
      (Decomp378b.zeroTerm_summable m X u hm hX hu hmu)
    have hf := weighted_formula_total m X u hm hX hu hmu
    linarith
  · exact Decomp359f.near_sum_le Decomp290a.verified_height m X u T hm hX hu hmu hT hTT
  · exact CountConvergence359.far_sum_le hN m X u T hm hX hu hmu hT

/-- P0099 pp. 18 to 20, Theorem 4 from the actual count premise.
CONDITIONAL ON that count premise, sharp prime sieve,
Schoenfeld bounds and finite-height RH citation. -/
theorem theorem4_of_lemma1 (hN : L1Zeta.Lemma1N) : Theorem4Fm L1Zeta.NZr 3300000000 :=
  Thm4LiteralZeta.theorem4Fm_of_zeta_lit Decomp290a.brun_titchmarsh Decomp290a.schoenfeld
    (display15 hN) Decomp290a.verified_height (L1Zeta.lemma1Count_zeta hN)

/-- P0099 pp. 18 to 20, exactly the original theorem4_cited target.
CONDITIONAL ON the new circle leaf, original Rosser count
and cutoff leaves, low_count, sharp prime sieve, Schoenfeld bounds and verified height. -/
theorem theorem4_cited : Theorem4Fm L1Zeta.NZr 3300000000 :=
  theorem4_of_lemma1 lemma1_two_sided

end LeanLab.RamareSaouter2003.Assembly378

#print axioms LeanLab.RamareSaouter2003.Assembly378.weighted_formula_total

#print axioms LeanLab.RamareSaouter2003.Assembly378.weighted_formula

#print axioms LeanLab.RamareSaouter2003.Assembly378.high_count

#print axioms LeanLab.RamareSaouter2003.Assembly378.lemma1_two_sided

#print axioms LeanLab.RamareSaouter2003.Assembly378.lemma1_cited

#print axioms LeanLab.RamareSaouter2003.Assembly378.display15

#print axioms LeanLab.RamareSaouter2003.Assembly378.theorem4_of_lemma1

#print axioms LeanLab.RamareSaouter2003.Assembly378.theorem4_cited
