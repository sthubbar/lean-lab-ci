/-
Split of the resolved core sum mean value of the local shoulder estimate of this
folder, one modulus at one residual. The target statement stays exactly as it is; this
file adds two leaves and one assembly.

The object of the target is the sum over the reduced residues of the modulus of the
square of the prime Fourier series against the phase of the residual, integrated over
the core of the arc, the interval of length two over N around the rational centre.
The core sum carries no main term: the phase has modulus one, so it contributes
nothing to the size, and the whole object is bounded by the local square mean value
alone.

Two steps do the work, and they are the two leaves. The first removes the phase: the
modulus of the squared series against the unit-modulus phase is the square of the
modulus of the series, so each residue class contributes at most the square mean value
of the series over its core interval. The second is the local square mean value itself:
on the core interval of one residue class of the modulus the square mean value of the
series is at most a constant times N log N to the thirteenth times the sum of the two
errors, divided by the modulus, which is the size the mean value alone supplies.

The assembly below only sums the amortised size over the reduced residues. There are at
most as many reduced residues as the modulus, so the sum of the amortised size is the
size itself, and the two constants are collected. No input is invented here.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_shoulder1622

namespace LeanLab.Linnik1951

/-- LEAF. The phase of the resolved core sum has modulus one. The squared prime Fourier
series at a point of the core, times the phase of the residual at that point, has the
modulus of the square of the modulus of the series alone; so the residual enters the
size of the core sum only through the point at which the series is taken, and not
through the phase. -/
theorem local_arc_shoulder1622_core_phase_norm (N : ℕ) (n : ℤ) (a q : ℕ) (z : ℝ) :
    ‖primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ =
      ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 := by
  have h₁ : ‖(primeFourier111 N ((a : ℝ) / q + z) : ℂ) ^ 2 *
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ =
    ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 := by
    have h₂ : ‖(primeFourier111 N ((a : ℝ) / q + z) : ℂ) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ =
      ‖(primeFourier111 N ((a : ℝ) / q + z) : ℂ) ^ 2‖ * ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ := by
      rw [Complex.norm_mul]
    rw [h₂]
    have h₃ : ‖(primeFourier111 N ((a : ℝ) / q + z) : ℂ) ^ 2‖ = ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 := by
      rw [norm_pow]
    rw [h₃]
    have h₄ : ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      have h₅ : (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I).re = 0 := by
        simp [Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        <;>
        ring_nf
        <;>
        norm_cast
        <;>
        simp_all [Complex.ext_iff, Complex.I_re, Complex.I_im]
        <;>
        linarith
      rw [h₅]
      norm_num [Real.exp_zero]
    rw [h₄]
    <;> ring
  exact h₁

/-- LEAF. The square mean value of one reduced residue on the core. The squared modulus
of the prime Fourier series at one residue class of the modulus, integrated over the
interval of length two over N around the rational centre, is bounded by the local
square mean value alone, amortised over the reduced residues: a constant times N log N
to the thirteenth times the sum of the two errors, divided by the modulus. The residual
does not occur, and neither a singular coefficient nor a Ramanujan sum nor a damped
convolution; the series itself is all that is estimated here. -/
theorem local_arc_shoulder1622_core_single_residue_square_mean (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ a : ℕ, Nat.Coprime a q →
        ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 ≤
          c * (N : ℝ) * Real.log N ^ 13 *
              (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) /
            (q : ℝ) := by
  sorry

/-- The interval triangle inequality on the core, with the phase removed: the core
integral of one residue class is at most the square mean value of the series over its
core interval. -/
private theorem local_arc_shoulder1622_core_term_norm_le (N : ℕ) (n : ℤ) (a q : ℕ)
    (hN : 0 < N) :
    ‖∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
        primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), ‖primeFourier111 N ((a : ℝ) / q + z)‖ ^ 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hle : -(1 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
    have h : (0 : ℝ) ≤ 1 / (N : ℝ) := div_nonneg zero_le_one hNr.le
    linarith
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm hle) ?_
  refine le_of_eq (intervalIntegral.integral_congr ?_)
  intro z hz
  exact local_arc_shoulder1622_core_phase_norm N n a q z

/-- The number of reduced residues of a modulus is at most the modulus, so summing the
amortised size over them costs nothing. -/
private theorem local_arc_shoulder1622_core_card_le (q : ℕ) :
    (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ (q : ℝ) := by
  have h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card ≤ (Finset.range q).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_range] at h
  exact_mod_cast h

/-- The amortised size is invariant under the cancellation of the modulus. -/
private theorem local_arc_shoulder1622_core_div_fold (c X : ℝ) (N q : ℕ)
    (hq : (q : ℝ) ≠ 0) :
    (q : ℝ) * (c * (N : ℝ) * Real.log N ^ 13 * X / (q : ℝ)) =
      c * (N : ℝ) * Real.log N ^ 13 * X := by
  field_simp

/-- The resolved core sum mean value, from the two mean value leaves: the phase costs
nothing, the square mean value supplies the amortised size, and the reduced residues are
at most the modulus in number. The target statement is unchanged. -/
theorem local_arc_shoulder1622_core_sum_mean_value_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N → ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤ c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, N0, hN0⟩ := local_arc_shoulder1622_core_single_residue_square_mean hG hM
  refine ⟨c, hc, N0, ?_⟩
  intro N hN q hq hqQ n hnN
  have hqpos : 0 < q := hq
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hYnn : (0 : ℝ) ≤ (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
      1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    have h1 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) :=
      div_nonneg zero_le_one (Real.rpow_pos_of_pos hNr _).le
    have h2 : (0 : ℝ) ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
    linarith
  have hBnn : (0 : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 *
      (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) / (q : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc.le hNr.le) (pow_nonneg hlog 13)) hYnn) hqr.le
  have hterm : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        c * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) / (q : ℝ) := by
    intro a ha
    have hac : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    exact le_trans (local_arc_shoulder1622_core_term_norm_le N n a q hNpos)
      (hN0 N hN q hq hqQ a hac)
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_right (local_arc_shoulder1622_core_card_le q) hBnn) ?_
  exact le_of_eq (local_arc_shoulder1622_core_div_fold c
    (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) N q
    (ne_of_gt hqr))

end LeanLab.Linnik1951
