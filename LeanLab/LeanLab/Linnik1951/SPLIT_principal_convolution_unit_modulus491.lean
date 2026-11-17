/-
Split of the unit modulus step of the principal convolution estimate of 491. The
target statement principal_convolution_unit_modulus491 stays exactly as it is; this
file adds three leaves and one assembly, and nothing else.

The three steps. At modulus one the reduced residue set is the single residue zero and
the character series is the full prime series, so the long arc is the one place where
the estimate has no reduced residue twist at all. There the principal square integral
is first replaced by the square integral of the model series S one on the same arc,
with the square root error term coming from the Cauchy Schwarz step; the Riemann
hypothesis enters only here, through the mean square of the principal character series
on the arc. Second, the arc integral of the model series is compared with the full
period integral, the difference being the two tails, which the decay of the model
coefficients bounds by the reciprocal of the arc length; the scale comparison turns
that into the reciprocal length error term. Third, the full period integral of the
squared model series is the exactly damped logarithmic convolution, which is an
identity and carries no error size at all. The assembly adds the two error sizes, uses
the identity to name the second endpoint, and folds both into the printed size.

No analytic input is invented here, and no declaration is introduced.
-/
import LeanLab.Linnik1951.SPLIT_principal_convolution491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. The arc comparison step, at unit modulus. The principal square integral over
the long arc is the square integral of the model series S one over the same arc up to
the square root error size, with no main term subtracted and no reduced residue twist
present. This is the Cauchy Schwarz step of the mean square estimate of the principal
character series on the arc, and it is the only leaf that uses the Riemann hypothesis;
the Mellin hypothesis is carried and not used. Every residual is allowed, in both
signs, and the modulus is one. -/
theorem principal_arc_compare_unit491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ, n ≤ N →
        ‖principalIntegral491 N q n -
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. The tail step, at unit modulus. The arc integral of the squared model series
differs from its full period integral by the two tails of length one half minus the
arc radius; the model coefficients decay like the reciprocal of the distance to the
nearest integer, so the tails are bounded by the reciprocal of the arc length, and the
scale comparison against the one tenth and one seventh powers of N turns that into the
reciprocal length error size. No main term occurs in this step. Every residual is
allowed, in both signs. -/
theorem logFourier_arc_tail_unit491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) -
          ∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. The exact full period step, at unit modulus. The full period integral of the
squared model series against the exponential phase is the exactly damped logarithmic
convolution, with the damping exp of minus the residual over N. This is an identity,
not an estimate: the model series is periodic with period one, its square against the
phase is periodic too, and the full period square integral is the convolution with
that damping, term by term. It holds for every integer residual and every N at least
one, and no error size appears. -/
theorem logFourier_full_period_unit491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) := by
  sorry

/-- The unit modulus step of the principal convolution estimate, assembled from the
three leaves. The statement is the sealed one, unchanged: the arc comparison gives the
square root size, the tail step gives the reciprocal length size, the exact full period
step names the endpoint, and the constants are added. -/
theorem principal_convolution_unit_modulus491_split (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ, 4 ≤ n → n ≤ N →
        ‖principalIntegral491 N q n -
          ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          C * (N : ℝ) * Real.log N ^ 13 *
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨C1, hC1, N1, h1⟩ := principal_arc_compare_unit491 hG
  obtain ⟨C2, hC2, N2, h2⟩ := logFourier_arc_tail_unit491
  refine ⟨C1 + C2, by positivity, max 8 (max N1 N2), ?_⟩
  intro N hN q hq hqQ hq1 n _hn4 hnN
  have hN8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hτ : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hR : (0 : ℝ) < ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := mul_pos hqpos hτ
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hJB : (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) = ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) :=
    logFourier_full_period_unit491 N (by omega) n
  rw [← hJB]
  have ha := h1 N hN1 q hq hqQ hq1 n hnN
  have hb := h2 N hN2 q hq hqQ hq1 n
  refine ((norm_sub_le_norm_sub_add_norm_sub (principalIntegral491 N q n) (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))).trans ?_)
  calc ‖principalIntegral491 N q n - (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ + ‖(∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - (∫ z in (-(1 / 2) : ℝ)..(1 / 2), logFourier520 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖
      ≤ C1 * (N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        C2 * (N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := add_le_add ha hb
    _ = C1 * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) + C2 * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    _ ≤ (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
        (C1 + C2) * ((N : ℝ) * Real.log N ^ 13 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      gcongr <;> linarith
    _ = (C1 + C2) * (N : ℝ) * Real.log N ^ 13 *
        (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring

end LeanLab.Linnik1951
