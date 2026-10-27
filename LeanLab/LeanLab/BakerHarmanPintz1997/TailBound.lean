/-
P0069, page 26, the elementary counting step in Heath Brown truncation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.MoebiusSieve
namespace LeanLab.BakerHarmanPintz1997
open Finset ArithmeticFunction
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
theorem powerset_tail_bound (P : Finset ℕ) (w : ℝ) (hP : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) < w)
    {γ : ℝ} (hγ : 1 < γ) :
    ‖∑ T ∈ P.powerset, if γ ≤ ((∏ p ∈ T, p : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0‖ ≤
      ∑ T ∈ P.powerset, if γ ≤ ((∏ p ∈ T, p : ℕ) : ℝ) ∧
        ((∏ p ∈ T, p : ℕ) : ℝ) < γ * w then (1 : ℝ) else 0 := by
  induction P using Finset.induction_on generalizing γ with
  | empty => simp [not_le.mpr hγ]
  | @insert p P hp ih =>
    have hp1 : 1 ≤ p := (hP p (mem_insert_self _ _)).1
    have hpw : (p : ℝ) < w := (hP p (mem_insert_self _ _)).2
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hP' : ∀ q ∈ P, 1 ≤ q ∧ (q : ℝ) < w := fun q hq => hP q (mem_insert_of_mem hq)
    have htail : (∑ T ∈ (insert p P).powerset,
        if γ ≤ ((∏ q ∈ T, q : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0) =
      (∑ T ∈ P.powerset, if γ ≤ ((∏ q ∈ T, q : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0) -
      ∑ T ∈ P.powerset, if γ / p ≤ ((∏ q ∈ T, q : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0 := by
      rw [sum_powerset_insert hp, sub_eq_add_neg, ← sum_neg_distrib]
      congr 1
      apply sum_congr rfl
      intro T hT
      have hpT : p ∉ T := fun h => hp ((mem_powerset.mp hT) h)
      have heq : γ ≤ (p : ℝ) * ((∏ q ∈ T, q : ℕ) : ℝ) ↔
          γ / p ≤ ((∏ q ∈ T, q : ℕ) : ℝ) := by rw [div_le_iff₀ hp0, mul_comm]
      simp only [prod_insert hpT, Nat.cast_mul, card_insert_of_notMem hpT, pow_succ, heq]
      split_ifs <;> ring
    have hcount : (∑ T ∈ (insert p P).powerset, if γ ≤ ((∏ q ∈ T, q : ℕ) : ℝ) ∧
        ((∏ q ∈ T, q : ℕ) : ℝ) < γ * w then (1 : ℝ) else 0) =
      (∑ T ∈ P.powerset, if γ ≤ ((∏ q ∈ T, q : ℕ) : ℝ) ∧
        ((∏ q ∈ T, q : ℕ) : ℝ) < γ * w then (1 : ℝ) else 0) +
      ∑ T ∈ P.powerset, if γ / p ≤ ((∏ q ∈ T, q : ℕ) : ℝ) ∧
        ((∏ q ∈ T, q : ℕ) : ℝ) < γ / p * w then (1 : ℝ) else 0 := by
      rw [sum_powerset_insert hp]
      congr 1
      apply sum_congr rfl
      intro T hT
      have hpT : p ∉ T := fun h => hp ((mem_powerset.mp hT) h)
      have hlo : γ ≤ (p : ℝ) * ((∏ q ∈ T, q : ℕ) : ℝ) ↔
          γ / p ≤ ((∏ q ∈ T, q : ℕ) : ℝ) := by rw [div_le_iff₀ hp0, mul_comm]
      have hhi : (p : ℝ) * ((∏ q ∈ T, q : ℕ) : ℝ) < γ * w ↔
          ((∏ q ∈ T, q : ℕ) : ℝ) < γ / p * w := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hp0, mul_comm]
      simp only [prod_insert hpT, Nat.cast_mul, hlo, hhi]
    rw [htail, hcount]
    by_cases hsmall : 1 < γ / (p : ℝ)
    · exact (norm_sub_le _ _).trans (add_le_add (ih hP' hγ) (ih hP' hsmall))
    · have hδ : γ / (p : ℝ) ≤ 1 := le_of_not_gt hsmall
      have hall : ∀ T ∈ P.powerset, γ / (p : ℝ) ≤ ((∏ q ∈ T, q : ℕ) : ℝ) := by
        intro T hT
        apply hδ.trans
        exact_mod_cast Finset.one_le_prod (fun q hq => (hP' q ((mem_powerset.mp hT) hq)).1)
      have heqall : (∑ T ∈ P.powerset,
          if γ / (p : ℝ) ≤ ((∏ q ∈ T, q : ℕ) : ℝ) then (-1 : ℂ) ^ T.card else 0) =
          ∑ T ∈ P.powerset, (-1 : ℂ) ^ T.card := by
        apply sum_congr rfl
        intro T hT
        exact ite_eq_left (hall T hT)
      rw [heqall]
      rcases P.eq_empty_or_nonempty with rfl | hne
      · have hbound : (p : ℝ) < γ * w := by
          have hw0 : 0 < w := hp0.trans hpw
          nlinarith
        have hγp : γ ≤ (p : ℝ) := by have := (div_le_iff₀ hp0).mp hδ; simpa using this
        have hscaled : (1 : ℝ) < γ / (p : ℝ) * w := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hp0]
          simpa using hbound
        simp only [powerset_empty, sum_singleton, prod_empty, card_empty, Nat.cast_one, pow_zero]
        simp [hδ, hscaled, not_le.mpr hγ]
      · have hz : (∑ T ∈ P.powerset, (-1 : ℂ) ^ T.card) = 0 := by
          exact_mod_cast sum_powerset_neg_one_pow_card_of_nonempty hne
        rw [hz, sub_zero]
        exact (ih hP' hγ).trans (le_add_of_nonneg_right (sum_nonneg (fun _ _ => by positivity)))

#print axioms powerset_tail_bound
end LeanLab.BakerHarmanPintz1997
