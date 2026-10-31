/-
P0044, Cai 2002. Decomposition of the Theorem on pages 597 to 598.
The written proof occupies pages 600 to 604.
AI wrote the Lean code. Binary Goldbach is open.
The four analytic leaves remain CONDITIONAL on the sources named below.
The assembly retains an explicit allowance for the error in display 4.1.
-/
import LeanLab.Cai2002.Sum41
import LeanLab.Cai2002.Numerics
import LeanLab.ChenExplicit.Reductions

open Filter Asymptotics

namespace LeanLab.Cai2002

/-- LEAF. Page 597 definition of C and page 604 final comparison.
The main scale is strictly positive once N is at least two. -/
theorem leaf118_scale_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2 := by
  have hC : 0 < C N := by
    unfold C
    exact mul_pos LeanLab.ChenExplicit.twinC_pos
      (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor N))
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (mul_pos hC (Real.rpow_pos_of_pos (by linarith) _))
    (sq_pos_of_pos (Real.log_pos hNr))

/-- LEAF. Page 601 display 4.1 with the explicit loss already proved in Sum41.
This is the weighted sieve reduction, before any analytic estimates. -/
theorem leaf118_weighted (N : ℕ) (hN : 177147 ≤ N) :
    (Ssift N 0.95 : ℝ) - (S1 N 0.95 : ℝ) / 2 - (S2 N 0.95 : ℝ) / 2 -
      (S3 N 0.95 : ℝ) - 3 * (N : ℝ) ^ (10 / 11 : ℝ) ≤ (S N 0.95 : ℝ) := by
  exact eq41_printed N 0.95 hN

/-- LEAF. Pages 601 and 604, absorption of the error in display 4.1.
The exponent 10/11 is smaller than 0.95 and C has a uniform positive lower bound. -/
theorem leaf118_loss :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      3 * (N : ℝ) ^ (10 / 11 : ℝ) ≤
        0.05 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  have hc := LeanLab.ChenExplicit.twinC_pos
  have ho : (fun n : ℕ => Real.log (n : ℝ) ^ 2) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (9 / 220 : ℝ)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (s := 9 / 220) (by norm_num)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.rpow_two] using h
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (ho.bound (show 0 < 0.05 * LeanLab.ChenExplicit.twinC / 3 by positivity))
  refine ⟨max n0 2, fun N hN => ?_⟩
  have hn : n0 ≤ N := (le_max_left ..).trans hN
  have hN2 : 2 ≤ N := (le_max_right ..).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) ^ 2 := sq_pos_of_pos (Real.log_pos hNr)
  have hh := hn0 N hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hNpos _)] at hh
  have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
    unfold C
    exact le_mul_of_one_le_right hc.le (LeanLab.ChenExplicit.one_le_oddFactor N)
  have hpow : (N : ℝ) ^ (0.95 : ℝ) =
      (N : ℝ) ^ (10 / 11 : ℝ) * (N : ℝ) ^ (9 / 220 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlog).mpr
  calc
    3 * (N : ℝ) ^ (10 / 11 : ℝ) * Real.log (N : ℝ) ^ 2 ≤
        3 * (N : ℝ) ^ (10 / 11 : ℝ) *
          ((0.05 * LeanLab.ChenExplicit.twinC / 3) * (N : ℝ) ^ (9 / 220 : ℝ)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 0.05 * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ)) := by
      rw [hpow]
      ring
    _ ≤ 0.05 * (C N * (N : ℝ) ^ (0.95 : ℝ)) := by
      gcongr

/-- LEAF. Page 601 display 4.4, including its sufficiently large threshold.
External inputs: Iwaniec, Rosser's sieve, 1981, pages 203 to 230;
Pan and Pan, Goldbach Conjecture, 1992, pages 175 to 176, Lemmas 2 and 3 here.
The integral constant alone is already proved in Integral44. -/
theorem leaf118_sieve_lower :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      12.9897 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) ≤
        (Ssift N 0.95 : ℝ) := by
  -- ATTEMPT lower 4: Using exact? directly without unformalized inputs is guaranteed to fail as the paper relies on external sieves.
  sorry

/-- LEAF. Page 602 display 4.7, including its sufficiently large threshold.
External inputs: Iwaniec's linear sieve and the Pan and Pan Bombieri theorem,
Lemmas 1 to 3 here. The integral constant alone is already proved in Integral47. -/
theorem leaf118_sieve_one :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤
        18.7347 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT one 4: Bounded search without the linear sieve inputs fails.
  sorry

/-- LEAF. Page 604 display 4.14, including its sufficiently large threshold.
External inputs: Iwaniec's linear sieve, Wu 1993, Quart. J. Math. 44,
pages 109 to 128, and Huxley's short interval prime number theorem in display 4.13.
The integral constant alone is already proved in Integral414. -/
theorem leaf118_sieve_two :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S2 N 0.95 : ℝ) ≤
        6.8086 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT two 4: Linear sieve, Wu and Huxley unformalized.
  sorry

/-- LEAF. Page 604 display 4.15, including its sufficiently large threshold.
External inputs: the same switching, linear sieve, Wu mean value theorem and
Huxley short interval theorem as display 4.14.
The integral constant alone is already proved in Integrals. -/
theorem leaf118_sieve_three :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  -- ATTEMPT three 4: Linear sieve, Wu and Huxley unformalized.
  sorry

/-- The exact cited MainTheorem, assembled from the leaves.
CONDITIONAL on the four analytic leaves. No sorry occurs in this assembly. -/
theorem main_theorem_decomp118 : MainTheorem := by
  obtain ⟨n0, h0⟩ := leaf118_loss
  obtain ⟨n1, h1⟩ := leaf118_sieve_lower
  obtain ⟨n2, h2⟩ := leaf118_sieve_one
  obtain ⟨n3, h3⟩ := leaf118_sieve_two
  obtain ⟨n4, h4⟩ := leaf118_sieve_three
  refine ⟨max 177147 (max n0 (max n1 (max n2 (max n3 n4)))), ?_⟩
  intro N he hN
  have hcut : 177147 ≤ N := (le_max_left ..).trans hN
  have hrest := (le_max_right ..).trans hN
  have hn0 : n0 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn1 : n1 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn2 : n2 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn3 : n3 ≤ N := (le_max_left ..).trans hrest
  have hn4 : n4 ≤ N := (le_max_right ..).trans hrest
  have hp := leaf118_scale_pos N (by omega)
  have hw := leaf118_weighted N hcut
  have hl := h0 N hn0
  have hs := h1 N he hn1
  have hs1 := h2 N he hn2
  have hs2 := h3 N he hn3
  have hs3 := h4 N he hn4
  have htarget :
      0.01 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) < (S N 0.95 : ℝ) := by
    linarith
  simpa only [mul_div_assoc, mul_assoc] using htarget

end LeanLab.Cai2002
