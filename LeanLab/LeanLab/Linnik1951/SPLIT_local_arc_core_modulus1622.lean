/-
Split of the local core estimate of the major arc file of this folder, one modulus
at one residual. The target statement stays exactly as it is; this file adds three
leaves and one assembly.

The core of an arc is the interval of length two over N around its centre. On the
core the prime square is resolved into residue classes modulo q. Two separate things
happen there. First, summing the resolved square over the reduced residues turns the
phase at the centre into the Ramanujan sum and the singular coefficient and leaves
the unshifted core integral; the difference between the resolved sum and that
coefficient times the unshifted integral is the first error. Second, the unshifted
core integral itself is the exponentially damped convolution of the main term, up to
the second error. The singular coefficient times the Ramanujan sum has modulus at
most one, which is what lets the second error be carried over to the first one
without a new constant.

No input is invented here: the three pieces are leaves, and the assembly below only
adds the two error sizes.
-/
import LeanLab.Linnik1951.SPLIT_arc_local_expansion1622

namespace LeanLab.Linnik1951

/-- LEAF. The residue step on the core. Summing the squared prime Fourier series,
resolved at the rational centre, over the reduced residues gives the singular
coefficient times the Ramanujan sum at the residual, times the unshifted core
integral, up to the first error. The damped convolution and its exponential do not
occur here. -/
theorem local_arc_core_residue_step1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The unshifted core integral. The integral of the squared prime Fourier
series against the phase of the residual over the interval of length two over N
around the origin is the exponentially damped convolution of the main term, up to
the second error. No residue class modulo q, no Ramanujan sum and no singular
coefficient occur here. -/
theorem local_arc_core_convolution_step1622 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ,
        (4 : ℤ) ≤ n →
        n ≤ N →
        ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- LEAF. The size of the singular coefficient. The square of the Moebius function
over the square of the totient, times the Ramanujan sum at any residual, has modulus
at most one. This is the factor that multiplies the unshifted core error: the
coefficient has modulus at most one over the totient, and the Ramanujan sum at a
fixed modulus has modulus at most the totient. -/
theorem local_arc_singular_coefficient1622 (q n : ℕ) :
    ‖(((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) *
      LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n‖ ≤ 1 := by
  sorry

/-- The local core estimate at a modulus above one, from the residue step, the
unshifted core integral and the size of the singular coefficient. The target
statement is unchanged. -/
theorem local_arc_core_modulus1622_split (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) : ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → 2 ≤ q → ∀ n : ℤ, (4 : ℤ) ≤ n → n ≤ N → ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤ c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c1, hc1, N1, h1⟩ := local_arc_core_residue_step1622 hG hM
  obtain ⟨c2, hc2, N2, h2⟩ := local_arc_core_convolution_step1622 hG hM
  refine ⟨c1 + c2, by linarith, max N1 N2, ?_⟩
  intro N hN q hq hqQ hq2 n hn4 hnN
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hb1 := h1 N hN1 q hq hqQ hq2 n hn4 hnN
  have hb2 := h2 N hN2 q hq hqQ hq2 n hn4 hnN
  have hb3 := local_arc_singular_coefficient1622 q n.toNat
  have hmul : ‖((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * ((∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤ ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ := by
    have h := mul_le_mul_of_nonneg_right hb3 (norm_nonneg ((∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)))
    rw [one_mul] at h
    rwa [norm_mul]
  have htri : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤
      ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ + ‖((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * ((∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ := by
    have hEq : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)) =
        ((∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * (∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))) + ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat) * ((∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) - ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)) := by ring
    rw [hEq]
    exact norm_add_le _ _
  have hsum : ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ))‖ ≤ c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) + c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
    le_trans htri (add_le_add hb1 (le_trans hmul hb2))
  have heq : c1 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) + c2 * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) = (c1 + c2) * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by ring
  rw [← heq]
  exact hsum

end LeanLab.Linnik1951
