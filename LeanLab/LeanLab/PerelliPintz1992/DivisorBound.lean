/-
P0070 Section 6, page 367, the elementary divisor bound used in 37.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A linear factor is bounded by a constant times any geometric progression with base above one. -/
theorem linear_le_geometric (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * a ^ k := by
  let C : ℝ := max 1 ((a - 1)⁻¹)
  have hC : 1 ≤ C := le_max_left _ _
  have hCd : 1 ≤ C * (a - 1) := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((a - 1)⁻¹))
      (show 0 ≤ a - 1 by linarith)
    rw [inv_mul_cancel₀ (show a - 1 ≠ 0 by linarith)] at hh
    exact hh
  refine ⟨C, hC, fun k => ?_⟩
  have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ a by linarith) k
  have hk := mul_le_mul_of_nonneg_left hCd (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    (k : ℝ) + 1 ≤ C + (k : ℝ) * (C * (a - 1)) := by linarith
    _ = C * (1 + (k : ℝ) * (a - 1)) := by ring
    _ ≤ C * a ^ k := mul_le_mul_of_nonneg_left hb (by linarith)

#print axioms linear_le_geometric


/-- The divisor estimate used in equation 37, uniform over every positive integer. -/
theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hCk⟩ := linear_le_geometric ((2 : ℝ) ^ ε)
    (Real.one_lt_rpow (by norm_num) hε)
  obtain ⟨P, hP⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  refine ⟨C ^ (P + 1), by positivity, fun n hn => ?_⟩
  let S := n.primeFactors
  let B := S.filter (fun p => p ≤ P)
  have hpoint : ∀ p ∈ S, (n.factorization p : ℝ) + 1 ≤
      (if p ≤ P then C else 1) * (p : ℝ) ^ (ε * (n.factorization p : ℝ)) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    rw [Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
    by_cases hsmall : p ≤ P
    · rw [ite_eq_left hsmall]
      have h2p := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hp2 hε.le
      exact (hCk (n.factorization p)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2p _) (by linarith))
    · rw [ite_eq_right hsmall, one_mul]
      have ht : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have hbase : (2 : ℝ) ^ (1 / ε) ≤ (p : ℝ) :=
          hP.trans (by exact_mod_cast (by omega : P ≤ p))
        have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / ε)) hbase hε.le
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at hh
        exact hh
      have hb : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one, add_comm] using
          one_add_mul_sub_le_pow (a := (2 : ℝ)) (by norm_num) (n.factorization p)
      exact hb.trans (pow_le_pow_left₀ (by norm_num) ht _)
  have htau : (n.divisors.card : ℝ) = ∏ p ∈ S, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have hprod := Finset.prod_le_prod₀
    (fun p (_hp : p ∈ S) => show 0 ≤ (n.factorization p : ℝ) + 1 by positivity) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hB : (∏ p ∈ S, if p ≤ P then C else 1) = C ^ B.card := by
    rw [← Finset.prod_filter]
    simp [B]
  have hBc : B.card ≤ P + 1 := by
    calc
      B.card ≤ (Finset.range (P + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        have hh := (Finset.mem_filter.mp hp).2
        exact Finset.mem_range.mpr (by omega)
      _ = P + 1 := Finset.card_range _
  have hCP : C ^ B.card ≤ C ^ (P + 1) := pow_le_pow_right₀ hC hBc
  have hrec : (∏ p ∈ S, (p : ℝ) ^ n.factorization p) = (n : ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hpow : (∏ p ∈ S, (p : ℝ) ^ (ε * (n.factorization p : ℝ))) = (n : ℝ) ^ ε := by
    have hterm : ∀ p : ℕ, (p : ℝ) ^ (ε * (n.factorization p : ℝ)) =
        ((p : ℝ) ^ n.factorization p) ^ ε := by
      intro p
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
      congr 1
      ring
    simp_rw [hterm]
    rw [Real.finsetProd_rpow S (fun p => (p : ℝ) ^ n.factorization p)
      (fun _ _ => by positivity) ε, hrec]
  rw [← htau, hB, hpow] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hCP (Real.rpow_nonneg (Nat.cast_nonneg n) ε))

#print axioms divisors_card_le_rpow

end
end LeanLab.PerelliPintz1992.Section6
