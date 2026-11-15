/-
P0093 pages 160 and 161, equations 6.1 through 6.3. The principal convolution
estimate assembled from the arc comparison of equation 6.1 and the full period
extension of equations 6.2 and 6.3. The statement is that of principal_convolution491
in Decomp491b, unchanged. No open input: principal_arc_mean_square491 is proved under
the Riemann hypothesis. The print gives no argument for the passage from equation 6.2
to equation 6.3; the route here is the formalizer's.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.PrincipalArc491
import LeanLab.Linnik1951.PrincipalTail491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- P0093 pages 160 and 161 equations 6.1 through 6.3. The principal square
integral is the exactly damped logarithmic convolution up to the two displayed
errors. Triangle inequality between principal_arc_compare491, which replaces the
print's equation 6.1 by a comparison with S one on the arc, and
logFourier_arc_convolution491, which replaces equations 6.2 and 6.3. No open input.
CONDITIONAL ON GRH only, used at modulus one. The Mellin hypothesis is carried and
not used. -/
theorem principal_convolution491_route (hG : LeanLab.DERZ1997.GRH) (_hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := principal_arc_compare491 hG
  obtain ⟨C2, hC2, N2, h2⟩ := logFourier_arc_convolution491
  refine ⟨C1 + C2, by positivity, max 1 (max N1 N2), ?_⟩
  intro N hN q hq hqQ n _
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0.le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hR : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hpow
  have hS : 0 < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := Real.sqrt_pos.mpr hR
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hX : 0 ≤ (N : ℝ) * Real.log N ^ 13 := by positivity
  have ha := h1 N hN1 q hq hqQ n
  have hb := h2 N hN2 q hq hqQ n
  have hA : 0 ≤ (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hB : 0 ≤ (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    positivity
  calc
    _ ≤ ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ +
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C1 * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        C2 * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := add_le_add ha hb
    _ = C1 * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        C2 * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    _ ≤ (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      gcongr <;> linarith
    _ = _ := by ring

end LeanLab.Linnik1951
