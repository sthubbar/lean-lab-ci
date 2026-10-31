import LeanLab.Ternary78.CanonicalCount104
import LeanLab.Ternary78.BennettZeroData
/-
AI wrote this Lean code. Binary Goldbach is open.
These bounds use the actual analytic zero occurrence type and canonical natural count.
The cited analytic input remains Bennett Theorem 1.1, arXiv 2005.02989 page 2.
-/

namespace LeanLab.Ternary78.Bennett
/-- CONDITIONAL ON BennettThm1_1 for the canonical count of actual zeros.
The gamma weighted sum over all actual zero occurrences converges for every sigma > 0.
No zero enumeration or count agreement assumption is needed. -/
theorem actual_gamma_summable {Q q : ℕ} [NeZero q] (hB : BennettThm1_1 canonicalCount Q)
    (hq : q ≤ Q) (hq1 : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun w : zeroOccurrences χ =>
      ‖Complex.Gamma ((σ : ℂ) + (w.val.1.im : ℂ) * Complex.I)‖) := by
  classical
  have hn := primitive_ne_one hq1 χ hχ
  let (n : ℕ) : Fintype {w : zeroOccurrences χ // |w.val.1.im| ≤ (n + 1 : ℝ)} :=
    @Fintype.ofFinite _ (zeroOccurrences_bounded_finite χ hn (n + 1 : ℝ))
  exact @summable_gamma_of_bennett canonicalCount Q q inferInstance hB hq hq1 χ hχ
    (zeroOccurrences χ) (fun w => w.val.1.im) inferInstance
    (fun n => canonicalCount_eq_card χ (n + 1 : ℝ)) σ hσ
#print axioms actual_gamma_summable

/-- CONDITIONAL ON BennettThm1_1 for the canonical count of actual zeros.
The exact Bennett grid lower sum is at most the convergent actual gamma zero sum.
All finite count identities and convergence hypotheses are discharged internally. -/
theorem actual_gamma_grid_lower {Q q : ℕ} [NeZero q] (hB : BennettThm1_1 canonicalCount Q)
    (hq : q ≤ Q) (hq1 : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : 0 < σ) (t : ℕ → ℝ) (ht : Monotone t)
    (ht0 : ∀ i, 0 ≤ t i) (k : ℕ) :
    weightedCount (gridLower χ t)
        (fun i => ‖Complex.Gamma ((σ : ℂ) + (t i : ℂ) * Complex.I)‖) k ≤
      ∑' w : zeroOccurrences χ,
        ‖Complex.Gamma ((σ : ℂ) + (w.val.1.im : ℂ) * Complex.I)‖ := by
  classical
  have hn := primitive_ne_one hq1 χ hχ
  let (n : ℕ) : Fintype {w : zeroOccurrences χ // |w.val.1.im| ≤ (n + 1 : ℝ)} :=
    @Fintype.ofFinite _ (zeroOccurrences_bounded_finite χ hn (n + 1 : ℝ))
  have hcut : {w : zeroOccurrences χ | |w.val.1.im| ≤ t k}.Finite :=
    Set.finite_coe_iff.mp (zeroOccurrences_bounded_finite χ hn (t k))
  let z := hcut.toFinset
  have hz (w : zeroOccurrences χ) : w ∈ z ↔ |w.val.1.im| ≤ t k := by
    simp [z]
  have hcount (i : ℕ) (hi : 0 < i) (hik : i ≤ k) :
      canonicalCount q χ (t i) = (heightSet z (fun w => w.val.1.im) t i).card := by
    simp only [heightSet, Nat.ne_of_gt hi, ite_false]
    exact canonicalCount_eq_card_filter χ hn z hz (ht hik)
  exact @gamma_real_tsum_lower_of_bennett canonicalCount Q q inferInstance hB hq hq1 χ hχ
    (zeroOccurrences χ) inferInstance (fun w => w.val.1.im) inferInstance
    (fun n => canonicalCount_eq_card χ (n + 1 : ℝ)) z σ hσ t ht ht0 k hcount

#print axioms actual_gamma_grid_lower

/-- MODEL consequence, CONDITIONAL ON BennettThm1_1 for canonicalCount
and an explicit numerical lower certificate. No such certificate is asserted here. -/
theorem actual_model_gap {q : ℕ} [NeZero q] (hB : BennettThm1_1 canonicalCount 300000)
    (hq : q ≤ 300000) (hq1 : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i) (k : ℕ)
    {S c N : ℝ}
    (hS : (∑' w : zeroOccurrences χ,
      ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (w.val.1.im : ℂ) * Complex.I)‖) ≤ S)
    (hcert : 0.985 ≤ weightedCount (gridLower χ t)
      (fun i => ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (t i : ℂ) * Complex.I)‖) k)
    (hc : 0 < c) (hc2 : c ≤ 0.495462) (hN0 : 0 < N) (hN : N ≤ 8.875e30) :
    LeanLab.Ternary78.Threshold.m78 * (c * N) ^ (1 / 8 : ℝ) < S * Real.sqrt 300000 := by
  have hlow := actual_gamma_grid_lower hB hq hq1 χ hχ
    (by norm_num : (0 : ℝ) < 7 / 8) t ht ht0 k
  exact LeanLab.Ternary78.Threshold.gap_open (hcert.trans (hlow.trans hS)) hc hc2 hN0 hN

#print axioms actual_model_gap

end LeanLab.Ternary78.Bennett
