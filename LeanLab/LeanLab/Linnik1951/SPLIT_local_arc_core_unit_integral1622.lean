/-
Split of the size of the core integral at the unit modulus, at one residual.

The target bounds, by a constant times N log N to the thirteenth times the sum of the
two errors, the modulus of the core integral, that is of the squared prime Fourier
series against the phase of the residual, integrated over the interval of length two
over N around the origin.

The argument below is the one the target needs and no more. The phase of the residual
has modulus one on the real axis, so the modulus of the integral is at most the
integral of the squared modulus of the prime Fourier series over the same interval.
That is the first leaf; it is an inequality between two integrals of the same function
and uses neither the residual nor any growth in N. The second leaf is the local square
mean value on the core, the only analytic input in this file: the integral of the
squared modulus of the prime Fourier series over the interval of length two over N is
at most a constant times N log N to the thirteenth divided by N to the one seventh.
Neither leaf mentions the other, the second carries the larger of the two errors the
target adds, and the assembly below only composes them and drops the smaller error as
the nonnegative quantity it is.

No input is invented here: the analytic step is a leaf, and everything proved below is
elementary.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_core_unit1622

namespace LeanLab.Linnik1951

/-- LEAF. The phase step. The exponential of the residual has modulus one at every real
point, so the modulus of the core integral of the squared prime Fourier series against
it is at most the integral, over the same interval of length two over N around the
origin, of the squared modulus of the prime Fourier series. This step carries no
constant, no logarithm, no power of N and no estimate on the series itself, and the
residual enters it only through the phase. -/
theorem local_arc_core_unit_phase1622 (N : ℕ) (n : ℤ) :
    ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
        primeFourier111 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤
      ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N z‖ ^ 2 := by
  have hle : -(1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    by_cases hN : (N : ℝ) = 0
    · simp [hN]
    · have hpos : (0 : ℝ) < (N : ℝ) := by
        by_contra h
        push_neg at h
        have hNnat : (N : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le N
        have : (N : ℝ) = 0 := le_antisymm h hNnat
        exact hN this
      have hdiv : (0 : ℝ) ≤ 1 / (N : ℝ) := div_nonneg zero_le_one hpos.le
      linarith
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hle) ?_
  refine intervalIntegral.integral_mono (by linarith) (by linarith) ?_ ?_
  · intro z hz
    have hphase : ‖Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp_ofReal_mul_I]
    calc ‖primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖
        = ‖primeFourier111 N z ^ 2‖ * ‖Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)‖ := by
          rw [norm_mul]
      _ = ‖primeFourier111 N z ^ 2‖ * 1 := by rw [hphase]
      _ = ‖primeFourier111 N z ^ 2‖ := by ring
      _ = ‖primeFourier111 N z‖ ^ 2 := by rw [norm_pow]
  · intro z hz
    positivity

/-- LEAF. The local square mean value on the core. The integral, over the interval of
length two over N around the origin, of the squared modulus of the prime Fourier series
is at most a constant times N log N to the thirteenth divided by N to the one seventh.
This is the analytic input of the file and the only place where the growth in N is
estimated; it carries no residual, no phase, no complex exponential and no Ramanujan
sum, and its right hand side is the larger of the two errors the target adds. -/
theorem local_arc_core_unit_mean_value1622 :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
      (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N z‖ ^ 2) ≤
        c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- The size of the core integral at the unit modulus, from the phase step and the
local square mean value on the core. The residual at the unit modulus is at least
four, so the modulus of its phase is one; the mean value supplies the larger error and
the smaller one is bounded below by zero. The target statement is unchanged. -/
theorem local_arc_core_unit_integral1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
            primeFourier111 N z ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, hmean⟩ := local_arc_core_unit_mean_value1622
  refine ⟨c, hc, 1, ?_⟩
  intro N hN q hq hqQ hq1 n hn4 hnN
  have hN2 : 2 ≤ N := by omega
  have hphase := local_arc_core_unit_phase1622 N n
  have hm := hmean N hN2
  refine le_trans hphase (le_trans hm ?_)
  subst hq1
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hlog : (0 : ℝ) ≤ Real.log N ^ 13 :=
    pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) 13
  have hcoef : (0 : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 :=
    mul_nonneg (mul_nonneg hc.le hNnn) hlog
  have hterm : (0 : ℝ) ≤ 1 / Real.sqrt (((1 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    div_nonneg zero_le_one (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hterm) hcoef

end LeanLab.Linnik1951
