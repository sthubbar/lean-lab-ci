/-
Split of the local shoulder arc mean value of this folder, one modulus at one
residual. The target statement stays exactly as it is; this file adds three
leaves and one assembly.

The object of the target is the norm of the local arc integral localArc1622 at
one modulus and one residual. That object is a finite sum over the reduced
residues of one interval integral. The assembly bounds the norm of the sum by
the sum of the norms, bounds each integral by the per residue estimate, and
uses the trivial count of the reduced residues to collect the constant. No
analytic input is invented here: the per residue estimate is the only analytic
leaf, and the assembly is a chain of triangle inequality and algebra.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_shoulder1622

namespace LeanLab.Linnik1951

/-- LEAF. Triangle inequality over the finite reduced residue sum. The norm of
the whole local arc integral is at most the sum of the norms of the one
integral per reduced residue. This is the structural first step of the
argument and involves no estimate. -/
theorem arc_norm_le_sum_norm_F760 (N q : ℕ) (n : ℤ) :
    ‖localArc1622 N q n‖ ≤
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ := by
  sorry

/-- LEAF. The per residue estimate. For each reduced residue a modulo q, the
norm of the one interval integral over the arc of length two over q N to the
one seventh is bounded by the local square mean value alone, contributing a
factor one over q times the two error sizes. This is the single analytic step
of the argument and is strictly smaller than the whole target because it is
one integral instead of the sum. -/
theorem local_arc_per_residue_bound_F760 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ a : ℕ,
        a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) → ∀ n : ℤ,
          n ≤ N →
          ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
              Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
            c * (N : ℝ) * Real.log N ^ 13 * (1 / (q : ℝ)) *
              (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The count of reduced residues. The number of natural numbers below q
that are coprime to q is at most q. This is the second structural step and
collects the factor one over q against the count in the assembly. -/
theorem reduced_residue_card_le_F760 (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card ≤ q := by
  sorry

/-- The local shoulder arc mean value, assembled from the triangle inequality,
the per residue estimate and the residue count. The target statement is
unchanged. -/
theorem local_arc_shoulder1622_arc_mean_value_F760 (hG : LeanLab.DERZ1997.GRH)
    (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, N0, hmain⟩ := local_arc_per_residue_bound_F760 hG hM
  refine ⟨c, hc, N0, ?_⟩
  intro N hN q hq hqQ n hnN
  have htri := arc_norm_le_sum_norm_F760 N q n
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hbracket : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) +
      1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    add_nonneg (div_nonneg zero_le_one hpow.le)
      (div_nonneg zero_le_one (Real.sqrt_nonneg _))
  have hcommon : (0 : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 * (1 / (q : ℝ)) * hbracket := by
    positivity
  have hper := hmain N hN q hq hqQ
  have hsum : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖) ≤
      c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
        1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    have hle : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (q : ℝ)) * hbracket := by
      intro a ha
      exact hper a ha n hnN
    have hsumle := Finset.sum_le_sum hle
    rw [Finset.sum_const, nsmul_eq_mul] at hsumle
    have hcard := reduced_residue_card_le_F760 q
    have hqfac : (0 : ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 * hbracket := by
      positivity
    have hcardmul : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (c * (N : ℝ) * Real.log N ^ 13 * (1 / (q : ℝ)) * hbracket) ≤
        c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      have hcardq : (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hcard
      calc (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
              (c * (N : ℝ) * Real.log N ^ 13 * (1 / (q : ℝ)) * hbracket)
          = (c * (N : ℝ) * Real.log N ^ 13 * hbracket) *
              (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * (1 / (q : ℝ)) := by ring
        _ ≤ (c * (N : ℝ) * Real.log N ^ 13 * hbracket) * (q : ℝ) * (1 / (q : ℝ)) := by
          have := mul_le_mul_of_nonneg_right hcardq (by positivity : (0:ℝ) ≤ c * (N : ℝ) * Real.log N ^ 13 * hbracket)
          have h2 := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ 1 / (q : ℝ))
          linarith
        _ = c * (N : ℝ) * Real.log N ^ 13 * hbracket := by
          field_simp
          ring
        _ = c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := rfl
    exact le_trans hsumle hcardmul
  exact le_trans htri hsum

end LeanLab.Linnik1951
