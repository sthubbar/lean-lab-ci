import LeanLab.Zhao2025.FiniteWeights

/-!
The nested exponential sum of display 1.10 for every finite case layout.
The analytic hypothesis is a repaired labelled case.
Case zero is CONDITIONAL ON SmallCaseZeroEstimates for 4.1, 4.3 and 4.4.
R and T are defined from the finite zero sums, so no splitting identity is assumed.
Source: Zhao 2025, displays 1.10, 2.28 and 3.14, pages 3, 7 and 9.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhao2025.Task56

/-- Head and tail zero sets are indexed once each. -/
def layoutZeros {ι : Type*} (k : Fin 11) (n : ℕ) (H B : ℕ → Finset ι) :
    LayoutIndex k n → Finset ι :=
  Sum.elim (fun i => H i.val) (fun i => B i.val)

/-- CONDITIONAL display 1.10 with S written as the actual inner exponential sum. -/
theorem display110_zero_sums {ι : Type*} (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (k : Fin 11) (n : ℕ) (l11 L : ℝ)
      (H B : ℕ → Finset ι) (lam : ι → ℝ),
      c0 ≤ l11 →
      CaseInputs k n l11 (fun i => residualSum (B i) lam L)
        (fun i => cappedSum (B i) lam L) (fun i => zeroSum (H i) lam) →
      ∑ i : LayoutIndex k n,
        (∑ j ∈ layoutZeros k n H B i, Real.exp (-(10 / 3 * lam j))) ^ 2 ≤ 1 - c1 := by
  refine ⟨gap c0, lt_min (by linarith) (by norm_num), ?_⟩
  intro k n l11 L H B lam hl h
  have he := (uniform_energy c0 hc0 k n l11
    (fun i => residualSum (B i) lam L) (fun i => cappedSum (B i) lam L)
    (fun i => zeroSum (H i) lam) hl h).2
  rw [← layout_square_sum] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases i with
  | inl j => rfl
  | inr j => exact (weight_split (B j.val) lam L).2.2

#print axioms display110_zero_sums

end LeanLab.Zhao2025.Task56
