/-
Theorem 6.1, P0029 pages 21 and 22.
OPEN leaves for Jules. The assembly is CONDITIONAL on these leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-- LEAF. Pages 21 and 22, weighted zero sum estimate after the explicit formula.
Cited inputs: Linnik 1944 and the log free density bound 6.1.
OPEN. The gap includes removal of proper prime powers, which positivity of psi alone
would not justify. No polynomial prime bound is claimed proved here. -/
theorem linnik_weighted_gap150 : ∃ L C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ a : ℕ, Nat.Coprime a q → ∃ X : ℕ,
      (X : ℝ) ≤ C * (q : ℝ) ^ L ∧
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n := by
  sorry

/-- LEAF. Page 22, extracting a prime after subtracting the proper prime powers.
OPEN elementary finite sum step. This avoids inferring a prime from psi positivity alone. -/
theorem prime_of_weighted_gap150 (q a X : ℕ)
    (hgap : (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q), vonMangoldt n) >
      ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = a % q ∧ ¬ n.Prime),
        vonMangoldt n) :
    ∃ p : ℕ, p.Prime ∧ p % q = a % q ∧ p ≤ X := by
  sorry

/-- Exactly the sealed Theorem61 proposition. CONDITIONAL on the two OPEN leaves. -/
theorem theorem61_decomposed150 : Theorem61 := by
  obtain ⟨L, C, hC, hgap⟩ := linnik_weighted_gap150
  refine ⟨L, max C 2, ?_⟩
  intro q hq a ha
  by_cases hq1 : q = 1
  · subst q
    refine ⟨2, Nat.prime_two, by omega, ?_⟩
    simpa using (le_max_right C (2 : ℝ))
  · obtain ⟨X, hX, hψ⟩ := hgap q (by omega) a ha
    obtain ⟨p, hp, hpa, hpX⟩ := prime_of_weighted_gap150 q a X hψ
    refine ⟨p, hp, hpa, ?_⟩
    exact (show (p : ℝ) ≤ X by exact_mod_cast hpX).trans
      (hX.trans (mul_le_mul_of_nonneg_right (le_max_left C 2) (Real.rpow_nonneg (Nat.cast_nonneg q) L)))

end LeanLab.BhowmikGrimmelt2026

set_option format.width 1000

#print axioms LeanLab.BhowmikGrimmelt2026.linnik_weighted_gap150
#print axioms LeanLab.BhowmikGrimmelt2026.prime_of_weighted_gap150
#print axioms LeanLab.BhowmikGrimmelt2026.theorem61_decomposed150
