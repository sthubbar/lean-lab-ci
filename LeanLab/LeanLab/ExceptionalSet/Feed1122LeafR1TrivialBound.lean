/-
Deepening of `leaf_R1_trivial_bound` of `Feed1122LeafEvenMoment`, the trivial bound before
display 33 of Brudern-Perelli 1998, P0082, p. 368: `|R₁(m)| ≤ ∫_0^1 |S(α)|² dα ≪ X log X`.
The Chebyshev half, `Σ_{P<p≤X} (log p)² ≤ 2 X log X`, is proved here from the primorial
bound of Mathlib; the analytic half, `‖R₁(m)‖ ≤ Σ_{P<p≤X} (log p)²`, is one MEDIUM leaf.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real Finset

/-- LEAF: the first inequality before display 33 of P0082, p. 368, together with Parseval:
`‖R₁(m)‖ ≤ ∫_𝔐 |S(α)|² dα ≤ ∫_0^1 |S(α)|² dα = Σ_{P<p≤X} (log p)²`, the last step by the
orthogonality of `e(αk)` on `[0,1]`. Class MEDIUM: norm of a set integral, monotonicity in
the measurable set `𝔐 ⊆ [0,1]`, and Parseval for a finite trigonometric sum. -/
theorem leaf_R1_le_sum_log_sq (P X : ℝ) (m : ℤ) :
    ‖R1 P X m‖ ≤ ∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  sorry

/-- Chebyshev's bound in the form used before display 33 of P0082: for `X ≥ 2`,
`Σ_{P<p≤X} (log p)² ≤ log X · θ(X) ≤ (log 4) X log X ≤ 2 X log X`. Proved from
`primorial_le_four_pow`. -/
theorem prime_log_sq_sum_le (P X : ℝ) (hX : 2 ≤ X) :
    (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2) ≤ 2 * X * Real.log X := by
  classical
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set n := ⌊X⌋₊ with hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0.le
  have hsub : (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hstep1 : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p ^ 2) ≤
      ∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log X * Real.log p := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hpX : (p : ℝ) ≤ X := le_trans (by exact_mod_cast hp.1.2) hnX
    have : Real.log p ≤ Real.log X := Real.log_le_log (by linarith) hpX
    nlinarith
  have hstep2 : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p) ≤
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => by
      simp only [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
  have hprim : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p) ≤ n * Real.log 4 := by
    have h1 : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p) =
        Real.log ((primorial n : ℕ) : ℝ) := by
      rw [primorial, Nat.cast_prod, Real.log_prod]
      intro p hp
      simp only [Finset.mem_filter] at hp
      exact_mod_cast hp.2.ne_zero
    rw [h1]
    have h4 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_four_pow n
    have hpos : (0 : ℝ) < ((primorial n : ℕ) : ℝ) := by exact_mod_cast primorial_pos n
    calc Real.log ((primorial n : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hpos h4
      _ = n * Real.log 4 := by rw [Real.log_pow]
  have hlog4 : Real.log 4 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 / 2 by norm_num)
    have h2 : Real.log 4 = Real.log (4/2) + Real.log 2 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h3 := Real.log_two_lt_d9
    linarith
  rw [← Finset.mul_sum] at hstep1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ Real.log X * ∑ p ∈ (Finset.Ioc ⌊P⌋₊ n).filter Nat.Prime, Real.log p := hstep1
    _ ≤ Real.log X * (n * Real.log 4) :=
        mul_le_mul_of_nonneg_left (hstep2.trans hprim) hlogX
    _ ≤ Real.log X * (X * 2) := by
        apply mul_le_mul_of_nonneg_left _ hlogX
        exact mul_le_mul hnX hlog4 (Real.log_nonneg (by norm_num)) hX0.le
    _ = 2 * X * Real.log X := by ring

/-- `leaf_R1_trivial_bound` of `Feed1122LeafEvenMoment`, statement unchanged, from the
leaf `leaf_R1_le_sum_log_sq` and the proved Chebyshev bound. -/
theorem leaf_R1_trivial_bound_of_leaves (P X : ℝ) (hX : 2 ≤ X) (m : ℤ) :
    ‖R1 P X m‖ ≤ 2 * X * Real.log X :=
  (leaf_R1_le_sum_log_sq P X m).trans (prime_log_sq_sum_le P X hX)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.prime_log_sq_sum_le
#print axioms LeanLab.ExceptionalSet.U1539.leaf_R1_trivial_bound_of_leaves
