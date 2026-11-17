/-
Split of the leaf principal_convolution_intermediate_modulus491 of
SPLIT_principal_convolution491. The sealed statement is kept exactly as it is; this
file adds two leaves and one assembly.

The intermediate modulus case is where a reduced residue twist is present but the arc
of the reduced fraction is still long against the modulus, so both displayed error
sizes are needed. The comparison of the principal square integral with the exactly
damped logarithmic convolution then goes through two separate steps, and only those
two steps are left open here:

  the arc step, which replaces the principal square integral by the square integral of
  the model series over the same arc and costs the reciprocal square root error;

  the full period step, which extends that arc integral of the model series square to
  a full period and reads off the damped logarithmic convolution, at the cost of the
  reciprocal length error.

Each leaf is the corresponding global comparison restricted to moduli between two and
the one twentieth power of N, so each is strictly weaker than the target. The assembly
is the triangle inequality between the two, with the two constants added and the two
error sizes folded into the single printed combination. No analytic input is invented
here and no hypothesis is dropped from the statement.
-/
import LeanLab.Linnik1951.SPLIT_principal_convolution491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The arc step of the intermediate modulus case. The principal square integral
over the arc of the reduced fraction is the square integral of the model series over
the same arc up to the reciprocal square root error, for every modulus between two and
the one twentieth power of N and every integer residual. This is the step that removes
the character prime series from the integrand by the second moment on the arc. -/
theorem principal_arc_compare_intermediate491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ,
        ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. The full period step of the intermediate modulus case. The arc integral of
the squared model series is the exactly damped logarithmic convolution up to the
reciprocal length error, for every modulus between two and the one twentieth power of N
and every integer residual. This is the step that extends the arc to a full period and
collects the single residue of the resulting geometric sum. -/
theorem logFourier_arc_convolution_intermediate491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ,
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- The intermediate modulus case of the principal convolution estimate, assembled from
the two comparison steps. The statement is the sealed one, unchanged. The difference of
the principal square integral and the damped convolution is split at the arc integral of
the model series square, each half is bounded by its own leaf, and the two constants are
added. -/
theorem principal_convolution_intermediate_modulus491_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := principal_arc_compare_intermediate491 hG
  obtain ⟨C2, hC2, N2, h2⟩ := logFourier_arc_convolution_intermediate491
  refine ⟨C1 + C2, by positivity, max 1 (max N1 N2), ?_⟩
  intro N hN q hq hqQ hq2 hq20 n _hn4 _hnN
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0.le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hR : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hpow
  have hS : 0 < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := Real.sqrt_pos.mpr hR
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have ha := h1 N hN1 q hq hqQ hq2 hq20 n
  have hb := h2 N hN2 q hq hqQ hq2 hq20 n
  have hA : 0 ≤ (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    positivity
  have hB : 0 ≤ (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    positivity
  calc
    _ ≤ ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ +
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C1 * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        C2 * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
      add_le_add ha hb
    _ = C1 * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        C2 * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    _ ≤ (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      gcongr <;> linarith
    _ = (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring

end LeanLab.Linnik1951
