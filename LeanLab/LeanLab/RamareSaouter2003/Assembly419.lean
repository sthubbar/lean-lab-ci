import LeanLab.RamareSaouter2003.Assembly378
import LeanLab.RamareSaouter2003.Decomp419a
import LeanLab.RamareSaouter2003.Decomp419b
import LeanLab.RamareSaouter2003.Decomp419c

/-!
P0099 p. 14 and pp. 18 to 20, with Rosser pp. 223 and 224.
The count estimate now uses the four smaller task419 source leaves.
The existing proved formula, convergence and near and far estimates are reused.
The finite-count and external prime estimates remain CONDITIONAL inputs.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Assembly419
open Real Complex Decomp359g Row1 Thm4Assembly Smooth

/-- Rosser p. 224, exactly the original powered_jensen_estimate target.
CONDITIONAL ON the two zeta envelope leaves and the Gamma summation identity.
The returning center and large powers are already proved. -/
theorem powered_jensen_estimate (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ K ≤ (N : ℝ) * ε ∧ poweredZeta T N 0 ≠ 0 ∧
      jensenFunctional T N ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + ε := by
  let q := Real.log (4 * 1.32 / 3)
  have hq : 0 < q := Real.log_pos (by norm_num)
  obtain ⟨L, hL⟩ := exists_nat_gt (max (K / ε) (Real.log 2 / (2 * q * ε)))
  obtain ⟨N, hN, hG, hret⟩ := PowerReturns359.powered_center_return T L (1 / 2) (by norm_num)
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hLN : (L : ℝ) < N := by exact_mod_cast hN
  have hKN : K ≤ (N : ℝ) * ε := by
    have hk := (le_max_left (K / ε) (Real.log 2 / (2 * q * ε))).trans hL.le
    have hh := (div_le_iff₀ hε).mp hk
    nlinarith
  have hsmall : Real.log 2 / (2 * q * N) ≤ ε := by
    have hk := (le_max_right (K / ε) (Real.log 2 / (2 * q * ε))).trans hL.le
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * q * ε)).mp hk
    apply (div_le_iff₀ (by positivity : 0 < 2 * q * N)).mpr
    have hm := mul_le_mul_of_nonneg_right hLN.le (by positivity : 0 ≤ 2 * q * ε)
    calc _ ≤ (L : ℝ) * (2 * q * ε) := hh
         _ ≤ (N : ℝ) * (2 * q * ε) := hm
         _ = _ := by ring
  have hcenter := Decomp378c.center_log_lower T N hret
  have hcircle := Decomp419c.circle_gamma_bound A T hA hFA hT N hN0
  have hdiv := div_le_div_of_nonneg_right (neg_le_neg hcenter)
    (by positivity : 0 ≤ 2 * q * N)
  have hcancel : (-(N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ + Real.log 2) /
        (2 * q * N) =
      -Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ / (2 * q) +
        Real.log 2 / (2 * q * N) := by
    field_simp [hq.ne', hNR.ne']
  refine ⟨N, hN0, hKN, hG, ?_⟩
  unfold jensenFunctional
  dsimp only [q] at hq hsmall hdiv hcancel
  rw [show -((N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ - Real.log 2) =
    -(N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ + Real.log 2 by ring,
    hcancel] at hdiv
  simp only [neg_div] at hdiv
  linarith


/-- Rosser 1941 pp. 223 and 224, exactly the existing high_count target.
CONDITIONAL ON the unchanged cutoff transition and the four task419 source leaves. -/
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
  · obtain ⟨k, hk, hcount⟩ := Decomp419b.powered_jensen_count A T hA hFA (le_of_lt (lt_of_not_ge hTA))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN, hkN, hG, hJ⟩ := powered_jensen_estimate A T hA hFA
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


/-- P0099 pp. 18 to 20, exactly the original Theorem 4 cited target.
CONDITIONAL ON four task419 leaves, the unchanged cutoff and low-count
certificates, and the original prime sieve, Schoenfeld and verified RH inputs. -/
theorem theorem4_cited : Theorem4Fm L1Zeta.NZr 3300000000 :=
  Assembly378.theorem4_of_lemma1 lemma1_two_sided

end LeanLab.RamareSaouter2003.Assembly419

#print axioms LeanLab.RamareSaouter2003.Assembly419.powered_jensen_estimate
#print axioms LeanLab.RamareSaouter2003.Assembly419.high_count
#print axioms LeanLab.RamareSaouter2003.Assembly419.lemma1_two_sided
#print axioms LeanLab.RamareSaouter2003.Assembly419.lemma1_cited
#print axioms LeanLab.RamareSaouter2003.Assembly419.theorem4_cited
