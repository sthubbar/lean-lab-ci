import LeanLab.Pintz2021.Reduction3

/-!
The prime difference Fourier identity in P0054 page 2 display 1.6
and page 3 display 1.9, on the existing period interval.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.DifferenceTask53

open Complex Finset MeasureTheory MinorArcs Reduction3
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher

/-- Orthogonality identifies the coefficient of the conjugated product. -/
theorem coef_S_mul_conj (a : ℕ → ℂ) (K m : ℕ) :
    coef (fun β => (∑ n ∈ range K, a n * e (n * β)) *
      (starRingEnd ℂ) (∑ n ∈ range K, a n * e (n * β))) m =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K,
        if n1 = n2 + m then a n1 * (starRingEnd ℂ) (a n2) else 0 := by
  unfold coef
  have hpt : ∀ β : ℝ,
      (∑ n ∈ range K, a n * e (n * β)) *
        (starRingEnd ℂ) (∑ n ∈ range K, a n * e (n * β)) * e (-(m * β)) =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K,
        (a n1 * (starRingEnd ℂ) (a n2)) *
          e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) := by
    intro β
    rw [map_sum, sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro n1 _
    rw [sum_mul]
    apply sum_congr rfl
    intro n2 _
    rw [map_mul, ← e_neg]
    have he : e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) =
        e (n1 * β) * e (-(n2 * β)) * e (-(m * β)) := by
      rw [← e_add, ← e_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  simp_rw [hpt]
  have hc : ∀ n1 n2 : ℕ, Continuous fun β : ℝ =>
      (a n1 * (starRingEnd ℂ) (a n2)) *
        e ((((n1 : ℤ) - n2 - m : ℤ) : ℝ) * β) :=
    fun n1 n2 => continuous_const.mul (continuous_e_mul _)
  rw [intervalIntegral.integral_finsetSum fun n1 _ =>
    (continuous_finsetSum _ fun n2 _ => hc n1 n2).intervalIntegrable _ _]
  apply sum_congr rfl
  intro n1 _
  rw [intervalIntegral.integral_finsetSum fun n2 _ => (hc n1 n2).intervalIntegrable _ _]
  apply sum_congr rfl
  intro n2 _
  rw [intervalIntegral.integral_const_mul, integral_e_int]
  by_cases h : n1 = n2 + m
  · simp [h]
  · have hz : ((n1 : ℤ) - n2 - m : ℤ) ≠ 0 := by omega
    simp [h, hz]

/-- The full weighted prime difference coefficient. -/
noncomputable def differenceR (X1 X : ℝ) (m : ℕ) : ℂ :=
  coef (fun β => S X1 X β * (starRingEnd ℂ) (S X1 X β)) m

/-- A prime difference whose two primes lie in the paper's cutoff interval. -/
def PrimeDifferenceIn (X1 X : ℝ) (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ X1 < p ∧ (p : ℝ) ≤ X ∧
    X1 < q ∧ (q : ℝ) ≤ X ∧ p = q + m

/-- Positive weighted coefficient supplies an actual prime difference. -/
theorem prime_difference_of_re_pos (X1 X : ℝ) (m : ℕ)
    (hpos : 0 < (differenceR X1 X m).re) : PrimeDifferenceIn X1 X m := by
  by_contra hnone
  have hz : differenceR X1 X m = 0 := by
    unfold differenceR S
    rw [coef_S_mul_conj]
    apply sum_eq_zero
    intro n1 _
    apply sum_eq_zero
    intro n2 _
    split_ifs with heq
    · by_contra hne
      have hn1 : aS X1 X n1 ≠ 0 := left_ne_zero_of_mul hne
      have hn2 : aS X1 X n2 ≠ 0 := by
        intro hn2
        apply right_ne_zero_of_mul hne
        simp [hn2]
      have hs1 : n1.Prime ∧ X1 < n1 ∧ (n1 : ℝ) ≤ X := by
        by_contra hbad
        exact hn1 (by simp [aS, hbad])
      have hs2 : n2.Prime ∧ X1 < n2 ∧ (n2 : ℝ) ≤ X := by
        by_contra hbad
        exact hn2 (by simp [aS, hbad])
      exact hnone ⟨n1, n2, hs1.1, hs2.1, hs1.2.1, hs1.2.2,
        hs2.2.1, hs2.2.2, heq⟩
    · rfl
  rw [hz, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The paper's norm squared integrand is the same full difference coefficient. -/
theorem differenceR_eq_norm_sq (X1 X : ℝ) (m : ℕ) :
    differenceR X1 X m = coef (fun β => ((‖S X1 X β‖ ^ 2 : ℝ) : ℂ)) m := by
  unfold differenceR
  congr 1
  funext β
  rw [Complex.mul_conj', Complex.ofReal_pow]

/-- The major part of the difference coefficient for a supplied minor set. -/
noncomputable def differenceR1 (S : ℝ → ℂ) (mi : Set ℝ) (m : ℕ) : ℂ :=
  coef (miᶜ.indicator fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) m

/-- The minor part of the difference coefficient. -/
noncomputable def differenceR2 (S : ℝ → ℂ) (mi : Set ℝ) (m : ℕ) : ℂ :=
  coef (mi.indicator fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) m

/-- A measurable split gives exactly the full difference coefficient. -/
theorem differenceR1_add_R2 (S : ℝ → ℂ) (hS : Continuous S)
    (mi : Set ℝ) (hmi : MeasurableSet mi) (m : ℕ) :
    differenceR1 S mi m + differenceR2 S mi m =
      coef (fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) m := by
  unfold differenceR1 differenceR2 coef
  have hF : IntervalIntegrable (fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) volume
      (-(1 / 2)) (1 / 2) :=
    (Complex.continuous_ofReal.comp (hS.norm.pow 2)).intervalIntegrable _ _
  have hem : ContinuousOn (fun β : ℝ => e (-(m * β)))
      (Set.uIcc (-(1 / 2)) (1 / 2)) := by
    simpa [neg_mul] using (continuous_e_mul (-(m : ℝ))).continuousOn
  have hi1 : IntervalIntegrable (fun β =>
      miᶜ.indicator (fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) β * e (-(m * β)))
      volume (-(1 / 2)) (1 / 2) :=
    IntervalIntegrable.mul_continuousOn
      ⟨hF.1.indicator hmi.compl, hF.2.indicator hmi.compl⟩ hem
  have hi2 : IntervalIntegrable (fun β =>
      mi.indicator (fun β => ((‖S β‖ ^ 2 : ℝ) : ℂ)) β * e (-(m * β)))
      volume (-(1 / 2)) (1 / 2) :=
    IntervalIntegrable.mul_continuousOn ⟨hF.1.indicator hmi, hF.2.indicator hmi⟩ hem
  rw [← intervalIntegral.integral_add hi1 hi2]
  congr 1
  funext β
  rw [← add_mul]
  congr 1
  by_cases hβ : β ∈ mi <;> simp [hβ]

end LeanLab.Pintz2021.DifferenceTask53

#print axioms LeanLab.Pintz2021.DifferenceTask53.coef_S_mul_conj
#print axioms LeanLab.Pintz2021.DifferenceTask53.prime_difference_of_re_pos
#print axioms LeanLab.Pintz2021.DifferenceTask53.differenceR_eq_norm_sq
#print axioms LeanLab.Pintz2021.DifferenceTask53.differenceR1_add_R2
