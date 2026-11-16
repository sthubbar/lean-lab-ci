/-
Split of localArc_core_small_residual_unit1622 for FREE-nv-glm4 task675.
This file creates 2-8 LEAF lemmas and an assembly theorem with no sorries.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_local_arc_small_residual1622

namespace LeanLab.Linnik1951

/-- LEAF. The sum over reduced residues modulo 1 has exactly one term at a = 0.
For q = 1, the set of reduced residues is {0}, and the filter keeps only a = 0.
This simplifies the sum to a single integral. -/
theorem LEAF_unit_modulus_sum_simplifies {N : ℕ} (n : ℤ) :
    (∑ a ∈ (Finset.range 1).filter (fun a => Nat.Coprime a 1),
      ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
        primeFourier111 N ((a : ℝ) / 1 + z) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / 1 + z) : ℝ) : ℂ) * Complex.I)) =
    ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
      primeFourier111 N z ^ 2 *
        Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
  sorry

/-- LEAF. The singular coefficient for q = 1 is 1.
Since moebius 1 = 1 and totient 1 = 1, the coefficient (moebius q)^2 / (totient q)^2 = 1. -/
theorem LEAF_unit_modulus_coefficient :
    (((ArithmeticFunction.moebius 1 : ℝ) ^ 2 / (1.totient : ℝ) ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
  sorry

/-- LEAF. The Ramanujan sum for q = 1 is 1 for any n.
The Ramanujan sum at modulus 1 is the sum over the single reduced residue a = 0 of exp(0) = 1. -/
theorem LEAF_unit_modulus_ramanujan (n : ℕ) :
    LeanLab.Perelli1996.Ramanujan103.ramanujanSum 1 n = 1 := by
  sorry

/-- LEAF. For n ≤ 3, the log convolution is zero.
This restates the vanishing lemma from the parent file. -/
theorem LEAF_log_conv_vanishes_small_residual {n : ℕ} (hn : n ≤ 3) :
    logConvolution1622 n = 0 := by
  sorry

/-- LEAF. The core error at unit modulus with small residual.
This bounds the integral of primeFourier111 N z ^ 2 * exp(2πi n z) over [-1/N, 1/N]
by the error term. -/
theorem LEAF_unit_core_small_residual_estimate (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ n : ℤ,
      n ≤ 3 →
      n ≤ N →
      ‖(∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)),
        primeFourier111 N z ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I))‖ ≤
        c * (N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  sorry

/-- Assembly theorem: localArc_core_small_residual_unit1622_F675.
This is the exact statement of the target theorem, proved from the LEAF lemmas above.
No sorries allowed in this proof. -/
theorem localArc_core_small_residual_unit1622_F675 (hG : LeanLab.DERZ1997.GRH) (hM : MellinBound280) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → q = 1 → ∀ n : ℤ,
        n ≤ 3 →
        n ≤ N →
        ‖(∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) - (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ)‖ ≤
          c * (N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
  obtain ⟨c₁, hc₁, N₀, h₁⟩ := LEAF_unit_core_small_residual_estimate hG hM
  refine' ⟨c₁, hc₁, N₀, ?_⟩
  intro N hN q hq hqQ hq1 n hn3 hnN
  have h₂ : (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N ((a : ℝ) / q + z) ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) = ∫ z in -(1 / (N : ℝ))..(1 / (N : ℝ)), primeFourier111 N z ^ 2 * Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I) := by
    have h₃ : q = 1 := hq1
    rw [h₃]
    have h₄ := LEAF_unit_modulus_sum_simplifies N n
    exact h₄
  rw [h₂]
  have h₃ : (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) * LeanLab.Perelli1996.Ramanujan103.ramanujanSum q n.toNat * ((Real.exp (-(n.toNat : ℝ) / N) * logConvolution1622 n.toNat : ℝ) : ℂ) = 0 := by
    have h₄ : q = 1 := hq1
    rw [h₄]
    have h₅ : logConvolution1622 n.toNat = 0 := LEAF_log_conv_vanishes_small_residual (by
      have h₆ : n.toNat ≤ 3 := by
        have h₇ : n ≤ 3 := hn3
        have h₈ : n.toNat ≤ 3 := by
          norm_cast at h₇ ⊢
          <;> omega
        exact h₈
      exact h₇)
    rw [h₅]
    simp [Complex.ext_iff, pow_two]
    <;> norm_num
    <;> simp_all [ArithmeticFunction.moebius, Nat.totient_prime]
    <;> norm_num
    <;> aesop
  rw [h₃]
  simp [norm_sub_rev]
  have h₄ := h₁ N hN n hn3 hnN
  have h₅ : (1 : ℝ) ≤ (N : ℝ) := by
    norm_cast
    <;> omega
  have h₆ : (1 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) = (1 : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) + 1 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have h₇ : q = 1 := hq1
    rw [h₇]
    <;> norm_num
  rw [h₆] at h₄
  exact h₄

end LeanLab.Linnik1951