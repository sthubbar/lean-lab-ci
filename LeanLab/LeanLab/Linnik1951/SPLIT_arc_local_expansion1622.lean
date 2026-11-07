/-
Unit U-1622. Split of the local major arc expansion of the major arc file of this
folder, one modulus at one residual. The target statement stays exactly as it is; this
file adds four leaves and one assembly.

The argument, from pages 159 to 161 of the source scan. The local square mean value on
one arc is at most a constant times N log N to the thirteenth over q N to the one
seventh. Every arc is the union of its core, the interval of length two over N around
its centre, and its shoulder, the rest. On the shoulder the phase is not resolved and
the mean value alone bounds the integral, which is the first error. On the core the
prime square sits at the rational centre, the sum over the reduced residues there gives
the Ramanujan sum and the singular coefficient, and the remaining integral over the
core gives the damped convolution of the target main term, which is the second error.
At a residual below four the convolution is empty, the main term vanishes, and only
the mean value is used.

No analytic input is invented here: the two local square statements are leaves, and
the assembly below only adds the two error sizes and splits on the residual.
-/
import LeanLab.Linnik1951.SPLIT1622_major

namespace LeanLab.Linnik1951

/-- The convolution sum is empty, hence zero, for a residual at most three. -/
private theorem logConvolution_eq_zero_of_le_three1622 {n : ℕ} (hn : n ≤ 3) :
    logConvolution1622 n = 0 := by
  unfold logConvolution1622
  exact Finset.sum_eq_zero (fun m hm => by
    simp only [Finset.mem_Icc] at hm
    omega)

/-- The same vanishing at an integer residual, in the form the assembly uses. -/
private theorem logConvolution_toNat_eq_zero1622 {n : ℤ} (hn : n ≤ 3) :
    logConvolution1622 n.toNat = 0 :=
  logConvolution_eq_zero_of_le_three1622 (by omega)

/-- LEAF. The shoulder step. On the part of every arc outside the interval of length
two over N around its centre the prime square integral is bounded by the local
mean value alone. This is the first error, of size N log N to the thirteenth over
N to the one seventh. No singular series, no Ramanujan sum and no main term occur
in it, and the residual enters only through the phase. -/
theorem local_arc_shoulder1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The core step at a modulus above one. On the interval of length two over N
around the centre of an arc the sum over the reduced residues of the prime square
with its phase is the singular coefficient times the Ramanujan sum at the residual,
and the integral over the core of the damped square is the damped convolution of
the main term. This is the second error only; the singular integral itself is not
estimated here. -/
theorem local_arc_core_modulus1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The core step at the unit modulus, where the reduced residue is only zero
and the singular coefficient and the totient both equal one. Same core estimate as
at a modulus above one, with the residual at least four. -/
theorem local_arc_core_unit1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The small residual step. At a residual at most three the convolution is an
empty sum, so the target main term vanishes and the local arc integral alone must
be bounded by the two error sizes. No singular series occurs. -/
theorem local_arc_small_residual1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- The local major arc expansion, from the two shoulder and core errors and the two
residual cases. The target statement is unchanged. -/
theorem arc_local_expansion1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, LocalExpansion1622 B N0 := by
  obtain ⟨c1, hc1, N1, h1⟩ := local_arc_shoulder1622 hG hM
  obtain ⟨c2, hc2, N2, h2⟩ := local_arc_core_modulus1622 hG hM
  obtain ⟨c3, hc3, N3, h3⟩ := local_arc_core_unit1622 hG hM
  obtain ⟨c4, hc4, N4, h4⟩ := local_arc_small_residual1622 hG hM
  refine ⟨c1 + c2 + c3 + c4, by positivity, max 8 (max N1 (max N2 (max N3 N4))), ?_⟩
  unfold LocalExpansion1622
  intro N hN q hq hqQ n hnN
  have hN8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hinner : max N1 (max N2 (max N3 N4)) < N :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hinner
  have hN2 : N2 < N :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_right _ _) hinner)
  have hN3 : N3 < N :=
    lt_of_le_of_lt (le_max_left _ _)
      (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_right _ _) hinner))
  have hN4 : N4 < N :=
    lt_of_le_of_lt (le_max_right _ _)
      (lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_right _ _) hinner))
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
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
  by_cases hn : n ≤ 3
  · have hL : logConvolution1622 n.toNat = 0 := logConvolution_toNat_eq_zero1622 hn
    have hM0 : (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) = 0 := by
      rw [hL]
      simp
    rw [hM0, sub_zero]
    have hb := h4 N hN4 q hq hqQ n hn hnN
    refine le_trans hb ?_
    have hcl : c4 ≤ c1 + c2 + c3 + c4 := by linarith
    have hstep := mul_le_mul_of_nonneg_right hcl hT
    calc c4 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
        = c4 * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
      _ ≤ (c1 + c2 + c3 + c4) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hstep
      _ = (c1 + c2 + c3 + c4) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
  · have hn4 : (4 : ℤ) ≤ n := by omega
    rcases eq_or_lt_of_le hq with hq1 | hq2
    · have hb1 := h1 N hN1 q hq hqQ n hnN
      have hb3 := h3 N hN3 q hq hqQ hq1.symm n hn4 hnN
      have htri : ‖localArc1622 N q n - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (localArc1622 N q n) (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))
      refine le_trans htri ?_
      have hsum : ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            c3 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add hb1 hb3
      refine le_trans hsum ?_
      have hcl : c1 + c3 ≤ c1 + c2 + c3 + c4 := by linarith
      have hstep := mul_le_mul_of_nonneg_right hcl hT
      calc c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            c3 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
          = (c1 + c3) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
        _ ≤ (c1 + c2 + c3 + c4) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hstep
        _ = (c1 + c2 + c3 + c4) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
    · have hb1 := h1 N hN1 q hq hqQ n hnN
      have hb2 := h2 N hN2 q hq hqQ hq2 n hn4 hnN
      have htri : ‖localArc1622 N q n - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (localArc1622 N q n) (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))
      refine le_trans htri ?_
      have hsum : ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
          c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add hb1 hb2
      refine le_trans hsum ?_
      have hcl : c1 + c2 ≤ c1 + c2 + c3 + c4 := by linarith
      have hstep := mul_le_mul_of_nonneg_right hcl hT
      calc c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
            c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
          = (c1 + c2) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
        _ ≤ (c1 + c2 + c3 + c4) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hstep
        _ = (c1 + c2 + c3 + c4) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring

end LeanLab.Linnik1951
