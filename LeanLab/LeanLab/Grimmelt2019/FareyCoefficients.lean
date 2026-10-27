/-
AI wrote this Lean code for CODEX task51.
P0074 page 8, summing the coefficients in Lemma 3.1.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.FareyExpansion

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- The coefficient attached to a reduced fraction in the model. -/
noncomputable def fareyCoeff (p : ℕ × ℕ) : ℂ :=
  (ArithmeticFunction.moebius p.1 : ℂ) / p.1.totient

/-- The norm of a coefficient is at most the reciprocal totient. -/
theorem fareyCoeff_norm_le {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ farey Q) :
    ‖fareyCoeff p‖ ≤ 1 / (p.1.totient : ℝ) := by
  have hφ : (0 : ℝ) < p.1.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by have := (mem_farey.mp hp).1; omega)
  have hμ : ‖(ArithmeticFunction.moebius p.1 : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
  unfold fareyCoeff
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hμ hφ.le

/-- Each individual coefficient has norm at most one. -/
theorem fareyCoeff_norm_le_one {Q : ℕ} {p : ℕ × ℕ} (hp : p ∈ farey Q) :
    ‖fareyCoeff p‖ ≤ 1 := by
  apply (fareyCoeff_norm_le hp).trans
  have hφ : (1 : ℝ) ≤ p.1.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by have := (mem_farey.mp hp).1; omega)
  exact (div_le_one (by linarith)).mpr hφ

/-- The total coefficient norm over all reduced fractions is at most Q. -/
theorem sum_fareyCoeff_norm_le (Q : ℕ) :
    ∑ p ∈ farey Q, ‖fareyCoeff p‖ ≤ (Q : ℝ) := by
  have hsum : ∑ p ∈ farey Q, ‖fareyCoeff p‖ =
      ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter
        (fun a => Nat.Coprime a q), ‖fareyCoeff (q, a)‖ := by
    exact sum_farey_by_denominator Q (fun p => ‖fareyCoeff p‖)
  rw [hsum]
  calc
    _ ≤ ∑ _q ∈ Finset.Icc 1 Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
      calc
        _ ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            1 / (q.totient : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          apply fareyCoeff_norm_le (Q := Q)
          exact mem_farey.mpr ⟨hqpos, (Finset.mem_Icc.mp hq).2,
            Finset.mem_range.mp (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
        _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
            rw [Nat.totient_eq_card_coprime]
            congr 1
            ext a
            simp only [Finset.mem_filter, Nat.coprime_comm]
          rw [hcard]
          exact mul_one_div_cancel hφ.ne'
    _ = (Q : ℝ) := by simp

/-- Uniform interval bounds cost only Q after all model coefficients are summed. -/
theorem weighted_farey_sum_le {Q : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ farey Q) (F : ℕ × ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ p ∈ S, ‖F p‖ ≤ B) :
    ‖∑ p ∈ S, fareyCoeff p * F p‖ ≤ B * Q := by
  calc
    _ ≤ ∑ p ∈ S, ‖fareyCoeff p * F p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S, ‖fareyCoeff p‖ * B := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hF p hp) (norm_nonneg _)
    _ = (∑ p ∈ S, ‖fareyCoeff p‖) * B := (Finset.sum_mul ..).symm
    _ ≤ (∑ p ∈ farey Q, ‖fareyCoeff p‖) * B := by
      gcongr
    _ ≤ (Q : ℝ) * B := mul_le_mul_of_nonneg_right (sum_fareyCoeff_norm_le Q) hB
    _ = B * Q := mul_comm _ _

#print axioms fareyCoeff_norm_le
#print axioms fareyCoeff_norm_le_one
#print axioms sum_fareyCoeff_norm_le
#print axioms weighted_farey_sum_le
end LeanLab.Grimmelt2019.MainTerm
