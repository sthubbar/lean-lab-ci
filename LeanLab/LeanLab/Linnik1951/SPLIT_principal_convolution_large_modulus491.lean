/-
Split of the large modulus step principal_convolution_large_modulus491 of
SPLIT_principal_convolution491. The sealed statement is kept exactly as it is; this
file adds two leaves and one assembly.

The large modulus regime is q between the one twentieth power of N and the tenth
power of N. There the arc of the reduced fraction, of half length one over q times
the seven seventh root of N, is short, and the comparison of the principal square
integral with the exactly damped logarithmic convolution goes through the same two
separated steps as in the unconditional route, each confined to this regime:

  the arc step, which replaces the principal square integral by the square integral
  of the model series over the same arc and costs the reciprocal square root error;

  the full period step, which extends that arc integral of the model series square to
  a full period and reads off the damped logarithmic convolution, at the cost of the
  reciprocal length error.

Each leaf is one of those two comparisons restricted to a modulus at least the one
twentieth power of N, so each is strictly weaker than the target: the target also
covers modulus one and the moduli below the one twentieth power, and neither leaf
asserts anything there. Both leaves are consistent with the residual range of the
target and with the degenerate end points: the modulus two, the residual four, and
empty residue sets are not excluded.

The assembly is the triangle inequality between the two steps, with the two
constants added and the two error sizes folded into the single printed combination.
No analytic input is invented here and no hypothesis of the statement is dropped.
-/
import LeanLab.Linnik1951.SPLIT_principal_convolution491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The arc step of the large modulus case. The principal square integral over
the arc of the reduced fraction is the square integral of the model series over the
same arc up to the reciprocal square root error, for every modulus between the one
twentieth power of N and the tenth power of N, every integer residual between four
and N. This is the step that removes the character prime series from the integrand
by the second moment on the arc; it asserts nothing at modulus one and nothing below
the one twentieth power. -/
theorem principal_arc_compare_large_modulus491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 /
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. The full period step of the large modulus case. The arc integral of the
model series square, with the residual exponential, is the exactly damped logarithmic
convolution up to the reciprocal length error, for every modulus between the one
twentieth power of N and the tenth power of N, every integer residual between four
and N. This is the step of the full period extension; it carries no character twist
and asserts nothing at modulus one and nothing below the one twentieth power. -/
theorem principal_full_period_large_modulus491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 /
            ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- The principal convolution estimate at a large modulus, assembled from the two
case steps. The statement is the sealed one, unchanged. The triangle inequality
passes from the principal square integral first to the arc integral of the model
series and then to the exactly damped convolution, and the two constants are added
and the two error sizes folded into the single printed combination. -/
theorem principal_convolution_large_modulus491_split (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        2 ≤ q → (N : ℝ) ^ (1 / 20 : ℝ) ≤ (q : ℝ) → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := principal_arc_compare_large_modulus491 hG
  obtain ⟨C2, hC2, N2, h2⟩ := principal_full_period_large_modulus491
  refine ⟨C1 + C2, by positivity, max 1 (max N1 N2), ?_⟩
  intro N hN q hq hqQ hq2 hqsmall n hn4 hnN
  have hN1 : N1 < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N2 < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN0 : 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0.le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hR : 0 < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hpow
  have hS : 0 < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := Real.sqrt_pos.mpr hR
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have ha := h1 N hN1 q hq hqQ hq2 hqsmall n hn4 hnN
  have hb := h2 N hN2 q hq hqQ hq2 hqsmall n hn4 hnN
  calc
    ‖principalIntegral491 N q n -
        ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
      ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ +
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C1 * (N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        C2 * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
      add_le_add ha hb
    _ = C1 * ((N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        C2 * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    _ ≤ (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      gcongr <;> linarith
    _ = _ := by ring

end LeanLab.Linnik1951
