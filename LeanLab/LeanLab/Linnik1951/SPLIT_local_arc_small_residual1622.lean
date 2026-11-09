/-
Split unit of U-1622. This file adds three leaves for the small residual case
local_arc_small_residual1622 of Linnik1951/SPLIT_arc_local_expansion1622.lean, plus
the assembly theorem local_arc_small_residual1622_split. No statement of the parent
file is changed and no definition is added; the leaves stay open here on purpose.

Route. Write tau for N to the one seventh and T for N times log N to the thirteenth
times the sum of one over tau and one over the square root of q times tau. The local
arc at a modulus q and a residual n is the sum over the reduced residues of the
integral of the square of the prime Fourier transform with its phase, taken over the
interval of length two over q tau around each rational centre. At a residual at most
three the damped convolution is an empty sum, so the singular term of the expansion
vanishes identically, and there is no main term left to estimate: the local arc is
controlled by the shoulder error, which the parent file already carries as a leaf and
which needs no lower bound on the residual, together with the core error at the small
residual, which is what this file splits out.

The core error is split at the modulus: one leaf for a modulus of at least two, one
for the unit modulus, where the only reduced residue is zero and the singular
coefficient and the totient are both one. Each leaf is one inequality with the two
sides used by the rest of the family, with the extra hypothesis that the residual is
at most three.

The assembly is the triangle inequality across the two error sizes and the vanishing
of the singular term. It uses the three leaves here and the shoulder leaf of the
parent file, never the small residual statement itself.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_arc_local_expansion1622

namespace LeanLab.Linnik1951

/-- LEAF. The vanishing step. At a residual at most three the damped convolution of
the main term is the empty sum, so it is zero. This is the identity that removes the
singular term from the expansion at a small residual. It holds for every residual at
most three, including zero. -/
theorem smallResidual_convolution_empty1622 {n : ℕ} (hn : n ≤ 3) :
    logConvolution1622 n = 0 := by
  have : Finset.Icc 2 (n - 2) = ∅ := by
    rw [Finset.Icc_eq_empty_iff]
    omega
  rw [logConvolution1622, this, Finset.sum_empty]

/-- LEAF. The core error at a small residual, for a modulus of at least two. Over the
interval of length two over N around each rational centre, the sum over the reduced
residues of the square of the prime Fourier transform with its phase differs from the
singular coefficient times the Ramanujan sum at the residual times the damped
convolution by at most the error T with one constant. The residual is at most three,
so the singular term on the right is zero by the vanishing leaf and this leaf is the
crude mean value estimate at the small residual. -/
theorem localArc_core_small_residual_modulus1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, N0, h⟩ := local_arc_core_modulus1622 hG hM
  use c, hc, N0
  intro N hN q hq hqQ hq2 n hn3 hnN
  have hL : logConvolution1622 n.toNat = 0 := smallResidual_convolution_empty1622 (by omega)
  have : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ = ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ := by
    rw [hL]
    simp
  rw [this]
  sorry

/-- LEAF. The same core error at a small residual for the unit modulus, where the only
reduced residue is zero, the singular coefficient is one and the totient is one. Same
two sides and the same error T as at a modulus of at least two, with the modulus fixed
to one and the residual at most three. -/
theorem localArc_core_small_residual_unit1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c, hc, N0, h⟩ := local_arc_core_unit1622 hG hM
  use c, hc, N0
  intro N hN q hq hqQ hq2 n hn3 hnN
  have hL : logConvolution1622 n.toNat = 0 := smallResidual_convolution_empty1622 (by omega)
  have : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ = ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ := by
    rw [hL]
    simp
  rw [this]
  sorry

/-- The small residual statement of the parent file, assembled from the vanishing of
the singular term and the two small residual core errors, with the shoulder error of
the parent file. No gap is left: one constant covers the unit modulus and every
modulus of at least two. -/
theorem local_arc_small_residual1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖localArc1622 N q n‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))  := by
  obtain ⟨c1, hc1, N1, h1⟩ := local_arc_shoulder1622 hG hM
  obtain ⟨c2, hc2, N2, h2⟩ := localArc_core_small_residual_modulus1622 hG hM
  obtain ⟨c3, hc3, N3, h3⟩ := localArc_core_small_residual_unit1622 hG hM
  refine ⟨c1 + c2 + c3, by positivity, max 8 (max N1 (max N2 N3)), ?_⟩
  intro N hN q hq hqQ n hn3 hnN
  have hN8 : 8 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hinner : max N1 (max N2 N3) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hinner
  have hN23 : max N2 N3 < N := lt_of_le_of_lt (le_max_right _ _) hinner
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_left _ _) hN23
  have hN3 : N3 < N := lt_of_le_of_lt (le_max_right _ _) hN23
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
  have hY1 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (1 / 7 : ℝ) := div_nonneg zero_le_one hpow.le
  have hY2 : (0 : ℝ) ≤ 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hY : (0 : ℝ) ≤ (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by linarith
  have hT : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    mul_nonneg (mul_nonneg hNr.le (pow_nonneg hlog 13)) hY
  have hL : logConvolution1622 n.toNat = 0 := smallResidual_convolution_empty1622 (by omega)
  have hS : (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) = 0 := by
    rw [hL]
    simp
  have hsh := h1 N hN1 q hq hqQ n hnN
  have htri : ‖localArc1622 N q n‖ ≤
      ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ := by
    have h := norm_add_le (localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))) (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
    rwa [sub_add_cancel] at h
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · have hc := h3 N hN3 q hq hqQ hq1.symm n hn3 hnN
    have hc' : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
        c3 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      rw [hS, sub_zero] at hc
      exact hc
    refine le_trans htri ?_
    have hsum : ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
        c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c3 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add hsh hc'
    refine le_trans hsum ?_
    have hcl : c1 + c3 ≤ c1 + c2 + c3 := by linarith
    have hstep := mul_le_mul_of_nonneg_right hcl hT
    calc c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c3 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
        = (c1 + c3) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
      _ ≤ (c1 + c2 + c3) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hstep
      _ = (c1 + c2 + c3) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
  · have hc := h2 N hN2 q hq hqQ hq2 n hn3 hnN
    have hc' : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
        c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      rw [hS, sub_zero] at hc
      exact hc
    refine le_trans htri ?_
    have hsum : ‖localArc1622 N q n - (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ + ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))‖ ≤
        c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := add_le_add hsh hc'
    refine le_trans hsum ?_
    have hcl : c1 + c2 ≤ c1 + c2 + c3 := by linarith
    have hstep := mul_le_mul_of_nonneg_right hcl hT
    calc c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) +
          c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))
        = (c1 + c2) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
      _ ≤ (c1 + c2 + c3) * ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := hstep
      _ = (c1 + c2 + c3) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring

end LeanLab.Linnik1951
