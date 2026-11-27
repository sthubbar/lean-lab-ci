/-
Split of the mixed local contribution estimate for the rational major arcs of
the circle-method decomposition in this folder.

The mixed contribution is the cross term of the exact square expansion of the
local prime series: twice the principal coefficient times the principal prime
series times the residue error, integrated over one centred local arc of radius
one over q times N to the one seventh, and summed over the reduced residues.

The estimate is cut into four smaller statements:

* the exact algebraic expansion of the cross term into a term with one full
  prime factor and a diagonal term in which the reduced residue sum collapses
  to the signed Ramanujan sum;
* the saving estimate for the reduced residue sum against one full prime
  factor;
* the estimate for the collapsed diagonal term;
* the elementary bound on the principal arithmetic coefficient.

The single assembly below adds the two bounded pieces and reads the target
display off the expansion.
-/
import LeanLab.Linnik1951.Decomp520a

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-- Splitting the constant out of the full-prime-factor sum. -/
private lemma mixed_shift_sum520 (N q : ℕ) (n : ℤ) :
    2 * principalCoefficient520 q *
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          2 * principalCoefficient520 q * principalPrime520 N q z *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z _
  ring

/-- Splitting the constant and the residue phase out of the diagonal sum. -/
private lemma mixed_diag_sum520 (N q : ℕ) (n : ℤ) :
    2 * principalCoefficient520 q ^ 2 *
      (signedRamanujan520 q n *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          2 * principalCoefficient520 q ^ 2 * principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) := by
  unfold signedRamanujan520
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [show 2 * principalCoefficient520 q ^ 2 *
      (Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      (2 * principalCoefficient520 q ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) from by ring]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z _
  dsimp only
  rw [centred_phase520 q a n z]
  ring

/-- LEAF. Expansion step. The residue error is the full prime series minus the
principal part, so the cross term multiplied out gives twice the principal
coefficient times the reduced residue sum of the principal part against one
full prime factor, minus twice the square of the principal coefficient times
the diagonal term. In the diagonal term the reduced residue sum of the phases
is the signed Ramanujan sum and only the centred phase survives. -/
theorem mixed_expansion520 (N q : ℕ) (n : ℤ) :
    mixedIntegral520 N q n =
      2 * principalCoefficient520 q *
          (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
                Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
        2 * principalCoefficient520 q ^ 2 *
          (signedRamanujan520 q n *
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              principalPrime520 N q z ^ 2 *
                Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) := by
  have hS := mixed_shift_sum520 N q n
  have hD := mixed_diag_sum520 N q n
  by_cases hq1 : 1 ≤ q
  · by_cases hN1 : 1 ≤ N
    · have hPc : Continuous (principalPrime520 N q) := continuous_principal520 N q hN1
      have hfc : Continuous (primeFourier111_up111 N) := continuous_prime_fourier111_up111 N hN1
      unfold mixedIntegral520 residueError520
      rw [hS, hD]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have h1 : IntervalIntegrable (fun z : ℝ => 2 * principalCoefficient520 q *
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
          volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        (by fun_prop : Continuous (fun z : ℝ => 2 * principalCoefficient520 q *
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) *
              Complex.I))).intervalIntegrable _ _
      have h2 : IntervalIntegrable (fun z : ℝ => 2 * principalCoefficient520 q ^ 2 *
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
          volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        (by fun_prop : Continuous (fun z : ℝ => 2 * principalCoefficient520 q ^ 2 *
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) *
              Complex.I))).intervalIntegrable _ _
      rw [← intervalIntegral.integral_sub h1 h2]
      apply intervalIntegral.integral_congr
      intro z _
      ring
    · have hN0 : N = 0 := by omega
      subst hN0
      have hA : -(1 / ((q : ℝ) * (((0 : ℕ) : ℝ)) ^ (1 / 7 : ℝ))) = 0 := by simp
      have hB : 1 / ((q : ℝ) * (((0 : ℕ) : ℝ)) ^ (1 / 7 : ℝ)) = 0 := by simp
      unfold mixedIntegral520 signedRamanujan520 residueError520
      rw [hA, hB]
      simp
  · have hq0 : q = 0 := by omega
    subst hq0
    simp [mixedIntegral520, signedRamanujan520, residueError520]


/-- LEAF. Saving step for one full prime factor. The reduced residue sum of the
principal part against one full prime series, weighted by the central phase and
taken over one centred local arc, is at most the scale N times the sixth power
of the logarithm of N divided by the square root of q times N to the one
seventh. This is the step in which the reduced residues are averaged and the
square root of the local radius is saved; it is the only place where the
arithmetic input enters. -/
theorem mixed_shifted_bound520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  exact mixed_shifted_prime_part520 hG

/-- LEAF. Diagonal step. In the diagonal term the residues have already been
summed, so what remains is the signed Ramanujan sum of the residual frequency
times the centred square of the principal prime series. That product is at most
the scale N times the sixth power of the logarithm of N divided by the square
root of q times N to the one seventh. -/
theorem mixed_diagonal_bound520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖signedRamanujan520 q n *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. Coefficient step. The principal arithmetic coefficient is the Mobius
value of the modulus divided by its totient, so its norm is at most one for
every positive modulus. -/
theorem mixed_coefficient_norm520 (q : ℕ) (hq : 1 ≤ q) :
    ‖principalCoefficient520 q‖ ≤ 1 := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hμ : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hc : principalCoefficient520 q =
      (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) := rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q.totient : ℝ))]
  rw [div_le_one (by linarith)]
  linarith


/-- The mixed estimate: the expansion turns the cross term into one term with a
single full prime factor and the collapsed diagonal term, the coefficient has
norm at most one, and the two saving estimates bound each piece by the common
scale, so their sum is bounded by twice the sum of the two constants. -/
theorem mixed_bound520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖mixedIntegral520 N q n‖ ≤ C * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨A, hA, NA, hSA⟩ := mixed_shifted_bound520 hG
  obtain ⟨B, hB, NB, hSB⟩ := mixed_diagonal_bound520 hG
  refine ⟨2 * A + 2 * B, by linarith, max NA NB, ?_⟩
  intro N hN q hq hqQ n hn
  have hNA : NA < N := lt_of_le_of_lt (le_max_left NA NB) hN
  have hNB : NB < N := lt_of_le_of_lt (le_max_right NA NB) hN
  have hS := hSA N hNA q hq hqQ n hn
  have hD := hSB N hNB q hq hqQ n hn
  have hc : ‖principalCoefficient520 q‖ ≤ 1 := mixed_coefficient_norm520 q hq
  rw [mixed_expansion520 N q n]
  set S : ℂ := ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) with hSdef
  set D : ℂ := signedRamanujan520 q n *
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        principalPrime520 N q z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) with hDdef
  have hS' : ‖S‖ ≤ A * (N : ℝ) * Real.log N ^ 6 /
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [hSdef]
    exact hS
  have hD' : ‖D‖ ≤ B * (N : ℝ) * Real.log N ^ 6 /
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [hDdef]
    exact hD
  set F : ℝ := (N : ℝ) * Real.log N ^ 6 /
    Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) with hF
  have hF0 : 0 ≤ F := by
    rw [hF]
    positivity
  have hSa : ‖S‖ ≤ A * F := by
    have he : A * F = A * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
      rw [hF]
      ring
    rw [he]
    exact hS'
  have hDa : ‖D‖ ≤ B * F := by
    have he : B * F = B * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
      rw [hF]
      ring
    rw [he]
    exact hD'
  have hfirst : ‖2 * principalCoefficient520 q * S‖ ≤ 2 * (A * F) := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, htwo]
    have hm : ‖principalCoefficient520 q‖ * ‖S‖ ≤ 1 * (A * F) :=
      mul_le_mul hc hSa (norm_nonneg _) (by linarith)
    have he : 2 * ‖principalCoefficient520 q‖ * ‖S‖ =
        2 * (‖principalCoefficient520 q‖ * ‖S‖) := by ring
    rw [he]
    linarith
  have hsecond : ‖2 * principalCoefficient520 q ^ 2 * D‖ ≤ 2 * (B * F) := by
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, norm_pow, htwo]
    have hc0 : (0 : ℝ) ≤ ‖principalCoefficient520 q‖ := norm_nonneg _
    have hc2 : ‖principalCoefficient520 q‖ ^ 2 ≤ 1 := by nlinarith
    have hm : ‖principalCoefficient520 q‖ ^ 2 * ‖D‖ ≤ 1 * (B * F) :=
      mul_le_mul hc2 hDa (norm_nonneg _) (by linarith)
    have he : 2 * ‖principalCoefficient520 q‖ ^ 2 * ‖D‖ =
        2 * (‖principalCoefficient520 q‖ ^ 2 * ‖D‖) := by ring
    rw [he]
    linarith
  calc ‖2 * principalCoefficient520 q * S - 2 * principalCoefficient520 q ^ 2 * D‖
      ≤ ‖2 * principalCoefficient520 q * S‖ + ‖2 * principalCoefficient520 q ^ 2 * D‖ :=
        norm_sub_le _ _
    _ ≤ 2 * (A * F) + 2 * (B * F) := by linarith
    _ = (2 * A + 2 * B) * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
        rw [hF]
        ring

end LeanLab.Linnik1951
