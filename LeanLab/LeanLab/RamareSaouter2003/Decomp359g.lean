import LeanLab.RamareSaouter2003.Decomp290b

/-!
Rosser 1941 pp. 223 and 224, Theorem 19 and its written proof.
The cited argument is Backlund pp. 354 to 375, especially displays 44 to 50.
The gamma argument is represented by the integral of the logarithmic derivative
along the vertical line with real part one quarter, starting at height zero.
This fixes the continuous argument used by Rosser, rather than a principal value.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp359g

open Real

/-- Rosser p. 224, the symmetrized N-th power used in Theorem 19. -/
noncomputable def poweredZeta (T : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (riemannZeta (z + 5 / 4 + T * Complex.I) ^ N +
    riemannZeta (z + 5 / 4 - T * Complex.I) ^ N) / 2

/-- Rosser p. 224, S of T. The gamma argument is continuously normalized
by integrating Gamma prime divided by Gamma from the positive real axis. -/
noncomputable def gammaRemainder (T : ℝ) : ℝ :=
  (∫ y in (0 : ℝ)..(T / 2),
    (deriv Complex.Gamma (1 / 4 + y * Complex.I) /
      Complex.Gamma (1 / 4 + y * Complex.I)).re) -
    T / 2 * Real.log (T / 2) + T / 2 + π / 8

/-- Rosser pp. 223 and 224, the displayed powered Jensen functional
without the constant k divided by N. Here r = 1.32 and q = log of 4r/3. -/
noncomputable def jensenFunctional (T : ℝ) (N : ℕ) : ℝ :=
  (∫ φ in (0 : ℝ)..π,
    Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
      (2 * π * Real.log (4 * 1.32 / 3) * N) +
    1 / 2 + 4 / (π * T) -
    Real.log ‖poweredZeta T N 0‖ / (2 * Real.log (4 * 1.32 / 3) * N) +
    |gammaRemainder T| / π

/-- LEAF. Rosser p. 223, Theorem 18 and the definition of A.
Only the finite transition from 1400 to the cutoff is included.
The source has A about 1467.47747 and M of A equal to 1041. -/
theorem cutoff_transition : ∃ A : ℝ, 1400 ≤ A ∧
    (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041 ∧
    ∀ T : ℝ, 1400 ≤ T → T ≤ A →
      |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤ 2 := by
  sorry

/-- LEAF. Rosser pp. 223 and 224, the displayed inequality in Theorem 19.
Backlund pp. 354 to 361, displays 44 to 50, supplies the argument principle
and Jensen step applied to powers of zeta. The contour estimate is not assumed. -/
theorem powered_jensen_count (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ N : ℕ, 0 < N → poweredZeta T N 0 ≠ 0 →
      |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
        jensenFunctional T N + k / N := by
  sorry

/-- LEAF. Rosser p. 224, bounds on the circle and the limiting choice of N.
Backlund pp. 361 to 375 gives the circle growth estimates.
This leaf bounds only the explicit Jensen functional. No zero count occurs.
The free K forces arbitrarily large powers and absorbs Rosser's k divided by N. -/
theorem powered_jensen_estimate (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ K ≤ (N : ℝ) * ε ∧ poweredZeta T N 0 ≠ 0 ∧
      jensenFunctional T N ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + ε := by
  sorry

/-- The exact high_count target of Decomp290b.
Rosser pp. 223 and 224, Theorem 19. CONDITIONAL ON the three source leaves. -/
theorem high_count (T : ℝ) (hT : 1400 ≤ T) :
    |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  obtain ⟨A, hA, hFA, hbase⟩ := cutoff_transition
  by_cases hTA : T ≤ A
  · have h := hbase T hT hTA
    have hlog : 6.9074 ≤ Real.log T := VerifyU1333.log_thousand_ge.trans
      (Real.log_le_log (by norm_num) (by linarith : (1000 : ℝ) ≤ T))
    have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg (by linarith)
    linarith
  · obtain ⟨k, hk, hcount⟩ := powered_jensen_count A T hA hFA (le_of_lt (lt_of_not_ge hTA))
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN, hkN, hG, hJ⟩ := powered_jensen_estimate A T hA hFA
      (le_of_lt (lt_of_not_ge hTA)) k (ε / 2) hk (by positivity)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hkdiv : k / (N : ℝ) ≤ ε / 2 := (div_le_iff₀ hNR).mpr (by nlinarith)
    have hc := hcount N hN hG
    linarith

end LeanLab.RamareSaouter2003.Decomp359g

#print axioms LeanLab.RamareSaouter2003.Decomp359g.poweredZeta
#print axioms LeanLab.RamareSaouter2003.Decomp359g.gammaRemainder
#print axioms LeanLab.RamareSaouter2003.Decomp359g.jensenFunctional
#print axioms LeanLab.RamareSaouter2003.Decomp359g.cutoff_transition
#print axioms LeanLab.RamareSaouter2003.Decomp359g.powered_jensen_count
#print axioms LeanLab.RamareSaouter2003.Decomp359g.powered_jensen_estimate
#print axioms LeanLab.RamareSaouter2003.Decomp359g.high_count
