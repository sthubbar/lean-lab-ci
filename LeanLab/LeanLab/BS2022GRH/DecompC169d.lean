/- AI wrote this Lean code for CODEX task169.
Theorem 4 and Table 1, journal pp. 1218 and 1219. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148f

namespace LeanLab.BS2022GRH.DecompC169d
open Real Finset Classical ChenThresholdGRH Decomp148f
noncomputable section

/-- Prime subsets with product below QD, p. 1219 remainder domain. -/
def subsets (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ) : Finset (Finset ℕ) :=
  (siftingPrimes P z).powerset.filter
    (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ Q, p : ℕ) * D)

/-- A finite sieve weight evaluated on the divisors of m, Theorem 4 proof input. -/
def weightValue (P : Set ℕ) (Q : Finset ℕ) (z D : ℝ)
    (w : Finset ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ T ∈ subsets P Q z D, if (∏ p ∈ T, p : ℕ) ∣ m then w T else 0

/-- The actual weighted divisor sum before replacing counts by their model, p. 1219. -/
def weightedActual (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (z D : ℝ) (w : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ subsets P Q z D, w T * ∑ m ∈ supp.filter (fun m => (∏ p ∈ T, p : ℕ) ∣ m), a m

/-- The same weighted sum with the multiplicative model, p. 1219 definition of r. -/
def weightedModel (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ) (w : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ subsets P Q z D, w T *
    ∑ m ∈ supp, a m * ∏ p ∈ (∏ q ∈ T, q : ℕ).primeFactors, g m p

/-- Interchange the two finite sums defining the actual weighted count. -/
theorem weighted_actual_eq (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) :
    weightedActual supp a P Q z D w =
      ∑ m ∈ supp, a m * weightValue P Q z D w m := by
  unfold weightedActual weightValue
  simp_rw [sum_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro T hT
  split_ifs <;> ring

/-- Weights of absolute value at most one cost at most the stated remainder R. -/
theorem weighted_error_le (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (g : ℕ → ℕ → ℝ) (z D : ℝ) (w : Finset ℕ → ℝ)
    (hw : ∀ T ∈ subsets P Q z D, |w T| ≤ 1) :
    |weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w| ≤
      errorSum supp a P Q g z D := by
  unfold weightedActual weightedModel
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  change |∑ T ∈ subsets P Q z D, w T * divisorError supp a g (∏ p ∈ T, p)| ≤ _
  calc
    _ ≤ ∑ T ∈ subsets P Q z D, |w T * divisorError supp a g (∏ p ∈ T, p)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ errorSum supp a P Q g z D := by
      unfold errorSum
      change (∑ T ∈ subsets P Q z D, _) ≤ ∑ T ∈ subsets P Q z D, _
      apply sum_le_sum
      intro T hT
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hw T hT) (abs_nonneg _)).trans_eq (one_mul _)

/-- A pointwise majorant gives an upper bound for the sifted sum. -/
theorem upper_of_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hw : ∀ m ∈ supp,
      (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ≤
        weightValue P Q z D w m) :
    sifted supp a P z ≤ weightedActual supp a P Q z D w := by
  rw [weighted_actual_eq]
  unfold sifted
  rw [sum_filter]
  apply sum_le_sum
  intro m hm
  have h := mul_le_mul_of_nonneg_left (hw m hm) (ha m)
  split_ifs at h ⊢ <;> simpa using h

/-- A pointwise minorant gives a lower bound for the sifted sum. -/
theorem lower_of_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ)
    (Q : Finset ℕ) (z D : ℝ) (w : Finset ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hw : ∀ m ∈ supp, weightValue P Q z D w m ≤
      (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0)) :
    weightedActual supp a P Q z D w ≤ sifted supp a P z := by
  rw [weighted_actual_eq]
  unfold sifted
  rw [sum_filter]
  apply sum_le_sum
  intro m hm
  have h := mul_le_mul_of_nonneg_left (hw m hm) (ha m)
  split_ifs at h ⊢ <;> simpa using h

/-- LEAF. Upper sieve weights and their model estimate, Theorem 4 p. 1218 and Table 1.
Construct the explicit Rosser weights from the cited Theorem 6 of arXiv 2207.09452.
The row 6100 supplies C1 equal to 112 at epsilon equal to 1/8349. -/
theorem upper_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    ∃ w : Finset ℕ → ℝ,
      (∀ T ∈ subsets P Q z D, |w T| ≤ 1) ∧
      (∀ m ∈ supp, (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0) ≤
        weightValue P Q z D w m) ∧
      weightedModel supp a P Q g z D w ≤
        (2 * exp eulerMascheroniConstant / (log D / log z) +
          (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z := by
  sorry

/-- LEAF. Lower sieve weights and their model estimate, Theorem 4 p. 1218 and Table 1.
The row 6100 supplies C2 equal to 114 at epsilon equal to 1/8349.
The signed minorant and absolute weight bound remain explicit obligations. -/
theorem lower_weights (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    ∃ w : Finset ℕ → ℝ,
      (∀ T ∈ subsets P Q z D, |w T| ≤ 1) ∧
      (∀ m ∈ supp, weightValue P Q z D w m ≤
        (if ∀ p ∈ siftingPrimes P z, ¬ p ∣ m then (1 : ℝ) else 0)) ∧
      (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z ≤
        weightedModel supp a P Q g z D w := by
  sorry

/-- Exact selected LinearSieveT4 from the two weight certificates.
All remainder bookkeeping is proved. The weight construction remains OPEN. -/
theorem linearSieveT4_8349 : LinearSieveT4 (1 / 8349) 112 114 := by
  intro supp a P Q g z D ha hsupp hP hQ hg _he0 _he1 hz hprod
  constructor
  · intro hzD hs
    obtain ⟨w, hw, hup, hmodel⟩ := upper_weights supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs
    have herr := weighted_error_le supp a P Q g z D w hw
    have hactual := upper_of_weights supp a P Q z D w ha hup
    have := le_abs_self (weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w)
    change sifted supp a P z ≤ _
    change _ ≤ (2 * exp eulerMascheroniConstant / (log D / log z) +
      (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z +
      errorSum supp a P Q g z D
    linarith
  · intro hzD hs
    obtain ⟨w, hw, hlo, hmodel⟩ := lower_weights supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs
    have herr := weighted_error_le supp a P Q g z D w hw
    have hactual := lower_of_weights supp a P Q z D w ha hlo
    have := neg_abs_le (weightedActual supp a P Q z D w - weightedModel supp a P Q g z D w)
    change _ ≤ sifted supp a P z
    change _ * mainMass supp a P g z - errorSum supp a P Q g z D ≤ _
    linarith

end
end LeanLab.BS2022GRH.DecompC169d

#print axioms LeanLab.BS2022GRH.DecompC169d.weighted_actual_eq
#print axioms LeanLab.BS2022GRH.DecompC169d.weighted_error_le
#print axioms LeanLab.BS2022GRH.DecompC169d.upper_of_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.lower_of_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.upper_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.lower_weights
#print axioms LeanLab.BS2022GRH.DecompC169d.linearSieveT4_8349
