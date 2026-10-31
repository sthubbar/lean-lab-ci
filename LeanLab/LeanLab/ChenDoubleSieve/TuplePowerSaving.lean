import LeanLab.ChenDoubleSieve.TupleLevel

/-!
# Power saving remainders for admissible tuples

Source: https://arxiv.org/pdf/0705.1652, page 9 equation 3.1,
and pages 15 and 17, Lemmas 4.1 and 4.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04

/-- The endpoint product is at most Q, with no distribution theorem assumed. -/
theorem endpoint_product_le_Q {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hU : UkData δ k N (n+1) V Δ) :
    (∏ j, V j) ≤ Q δ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW : 1 ≤ W δ k N := Real.one_le_rpow hNr (pow_nonneg hδ _)
  have hprod : 0 ≤ ∏ j, V j := prod_nonneg fun j hj => by linarith [hU.lower j]
  exact (le_mul_of_one_le_right hprod hW).trans (endpoint_product_level (by omega) hU)

/-- All reciprocal sieve exponents in the printed range preserve the tenth power lower bound. -/
theorem residual_power_ge {δ Δ sp : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hU : UkData δ k N (n+1) V Δ)
    (hsp : 0 < sp) (hsp10 : sp ≤ 10) {t : Fin (n+1) → ℕ}
    (ht : t ∈ Wu41.Tset N (n+1) V Δ) :
    (N : ℝ) ^ (δ ^ (k+1)/10) ≤ (Q δ N/(modulus t : ℝ)) ^ (1/sp) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW : 1 ≤ W δ k N := Real.one_le_rpow hNr (pow_nonneg hδ _)
  have hbase := hW.trans (residual_level_ge_W (by omega) hU ht)
  exact (residual_tenth_power (by omega) hU ht).trans
    (Real.rpow_le_rpow_of_exponent_le hbase (one_div_le_one_div_of_le hsp hsp10))

/-- The exact tuple error is bounded by a single power with an explicit coefficient. -/
theorem tuple_power_remainder {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 1 ≤ N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hU : UkData δ k N (n+1) V Δ) :
    ((n+1 : ℕ) : ℝ) * ((N : ℝ)/(N : ℝ)^(δ^(k+1)/10) +
      2^(n+1) * ∏ j, V j) ≤
      k * (1+2^k) * (N : ℝ)^(1-δ^(k+1)/10) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW : 1 ≤ W δ k N := Real.one_le_rpow hNr (pow_nonneg hδ0.le _)
  have hp : 0 ≤ ∏ j, V j := prod_nonneg fun j hj => by linarith [hU.lower j]
  apply Wu04Remainder.remainder_power_saving hNr le_rfl hδ0.le hU.count hp
    (endpoint_product_le_Q hN hδ0.le hU)
  have he := (Wu04Remainder.eta_bounds hδ0 hδ1 k).2
  linarith

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.endpoint_product_le_Q
#print axioms LeanLab.ChenDoubleSieve.Wu04.residual_power_ge
#print axioms LeanLab.ChenDoubleSieve.Wu04.tuple_power_remainder
