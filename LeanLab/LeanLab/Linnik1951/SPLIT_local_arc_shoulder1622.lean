/-
Split of the local shoulder estimate of the major arc file of this folder, one modulus
at one residual. The target statement stays exactly as it is; this file adds two
leaves and one assembly.

The argument, from pages 159 to 161 of the source scan. The object of the target is
the difference between the local arc integral I_q at the residual and the sum over the
reduced residues of the resolved square integral over the core of the arc, the
interval of length two over N around the rational centre. Neither object has a main
term in it: the shoulder step bounds the arc integral by the local square mean value
alone, because on the shoulder the phase is not resolved, and the resolved core sum
is bounded by the same mean value. The assembly below only adds the two sizes by the
triangle inequality and collects the two constants, which is why the target carries
the sum of the two errors and not the main term.

No input is invented here: the two mean value statements are leaves, and the assembly
below only adds the two error sizes.
-/
import LeanLab.Linnik1951.SPLIT_arc_local_expansion1622

namespace LeanLab.Linnik1951

/-- LEAF. The shoulder step on the arc itself. The local arc integral at one modulus
and one residual, summed over the reduced residues and integrated over the interval of
length two over q N to the one seventh around each rational centre, is bounded by the
local square mean value alone. On the shoulder the phase is not resolved, so no
singular series, no Ramanujan sum and no main term occur; this is the first error, of
size N log N to the thirteenth over N to the one seventh. -/
theorem local_arc_shoulder1622_arc_mean_value (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The shoulder step on the resolved core sum. The sum over the reduced residues
of the squared prime Fourier series against its phase, integrated over the core of
length two over N around each rational centre, is bounded by the same local square mean
value alone. The phase at the rational centre is carried only through its modulus, so
the singular coefficient, the Ramanujan sum and the damped convolution do not occur;
this is the second error, of the same size as the first. -/
theorem local_arc_shoulder1622_core_sum_mean_value (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The local shoulder estimate, from the two mean value leaves and the triangle
inequality. The target statement is unchanged. -/
theorem local_arc_shoulder1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c1, hc1, N1, h1⟩ := local_arc_shoulder1622_arc_mean_value hG hM
  obtain ⟨c2, hc2, N2, h2⟩ := local_arc_shoulder1622_core_sum_mean_value hG hM
  refine ⟨c1 + c2, by linarith, max N1 N2, ?_⟩
  intro N hN q hq hqQ n hnN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le N1) hN1
  have hb1 := h1 N hN1 q hq hqQ n hnN
  have hb2 := h2 N hN2 q hq hqQ n hnN
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hY1 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) := div_nonneg zero_le_one hpow.le
  have hY2 : (0 : ℝ) ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hY : (0 : ℝ) ≤ (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by linarith
  have hT : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    mul_nonneg (mul_nonneg hNr.le (pow_nonneg hlog 13)) hY
  refine le_trans (norm_sub_le _ _) ?_
  calc ‖localArc1622 N q n‖ +
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖
      ≤ c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add hb1 hb2
    _ = (c1 + c2) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
    _ = (c1 + c2) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring

end LeanLab.Linnik1951
