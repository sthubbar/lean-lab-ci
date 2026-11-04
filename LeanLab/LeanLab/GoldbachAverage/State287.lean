import LeanLab.GoldbachAverage.GSRHMajorant
import LeanLab.GoldbachAverage.GSAnalyticInputs

/-!
P0051 page 5 Theorem 5 B, the implication from eq. 30 to its two consequences.
This proposition is stated for reviewer inspection and is not asserted as a theorem.
The elementary implication from a majorant bound to the psi bound is proved separately.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.State287

/-- CITED. P0051 page 5 Theorem 5 B, from eq. 30 to the final two bounds.
This paper statement requires Claude statement review before merge. -/
def Theorem5BVarianceConsequence : Prop :=
  RiemannHypothesis →
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ x →
    GSInputs.J x h ≤ C * h * x * Real.log x) →
  ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
    (∀ N : ℕ, 2 ≤ N →
      Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ C₁ * N * Real.log N ^ 2) ∧
    (∀ N : ℕ, 2 ≤ N →
      |Chebyshev.psi N - N| ≤ C₂ * Real.sqrt N * Real.log N ^ ((3 : ℝ) / 2))

/-- P0051 page 5 Theorem 5 B, the elementary psi consequence of the majorant bound.
CONDITIONAL ON the displayed uniform majorant estimate. Theorem 3 supplies the square bound. -/
theorem psi_of_majorant_log_two (K : ℝ)
    (hK : ∀ N : ℕ, 2 ≤ N →
      Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤ K * N * Real.log N ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      |Chebyshev.psi N - N| ≤ C * Real.sqrt N * Real.log N ^ ((3 : ℝ) / 2) := by
  refine ⟨Real.sqrt (120 * max K 0), by positivity, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hu : Emajorant N (Real.exp (-(1 / (N : ℝ)))) ≤
      max K 0 * N * Real.log N ^ 2 := by
    refine (hK N hN).trans ?_
    gcongr
    exact le_max_left K 0
  have hp : (Real.log N ^ ((3 : ℝ) / 2)) ^ 2 = Real.log N ^ 3 := by
    rw [← Real.rpow_mul_natCast hl0]
    norm_num
  have hsq : (Chebyshev.psi N - N) ^ 2 ≤
      (Real.sqrt (120 * max K 0) * Real.sqrt N * Real.log N ^ ((3 : ℝ) / 2)) ^ 2 := by
    calc _ ≤ 120 * Emajorant N (Real.exp (-(1 / (N : ℝ)))) * Real.log N :=
        gs_theorem3_bound_sq N hN
      _ ≤ 120 * (max K 0 * N * Real.log N ^ 2) * Real.log N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num)) hl0
      _ = _ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hN0, hp]
        ring
  have hsqabs : |Chebyshev.psi N - N| ^ 2 ≤
      (Real.sqrt (120 * max K 0) * Real.sqrt N * Real.log N ^ ((3 : ℝ) / 2)) ^ 2 := by
    rwa [sq_abs]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hsqabs

end LeanLab.GoldbachAverage.State287
