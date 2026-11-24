/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`F2085.leaf_case2_F2085`, ROUTE BURST S98 burst-20261122, Case 2 of the proof
of Lemma 3.4 on page 11 with x = Y, y = H, (m, k) = (1, m).

* `case2_coeff_F2085`: the block coefficient of display 42 is the divisor sum
  of a_d = mu(d) on z smooth d in the block 2^j at most d below 2^(j+1).
  Proved.
* `leaf_lemma32_window_F2085`: Lemma 3.2 of page 10 for such a_d and b_k = 1,
  with L^B below 2^j at most H Y^(-1/2) L^(-B). LEAF, HARD.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_first_sum_F2085

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- Proved. The block coefficient of display 42, P0088 page 11, as a divisor sum
of the coefficient b_r = mu(r) on z smooth r in the dyadic block. -/
theorem case2_coeff_F2085 (z : ℝ) (j m : ℕ) :
    (∑ d ∈ (m.divisors.filter
        (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
        (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
    ∑ d ∈ m.divisors,
      (if (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z) ∧
          ((2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j)
        then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0) := by
  rw [Finset.filter_filter, Finset.sum_filter]

/-- Proved. The coefficient b_r is bounded by 1 and supported on the block. -/
theorem case2_coeff_bound_F2085 (z : ℝ) (j r : ℕ) :
    ‖(if (∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) < z) ∧
          ((2 : ℝ) ^ j ≤ (r : ℝ) ∧ (r : ℝ) < 2 * 2 ^ j)
        then ((ArithmeticFunction.moebius r : ℤ) : ℂ) else 0)‖ ≤ 1 ∧
    ((if (∀ p : ℕ, p.Prime → p ∣ r → (p : ℝ) < z) ∧
          ((2 : ℝ) ^ j ≤ (r : ℝ) ∧ (r : ℝ) < 2 * 2 ^ j)
        then ((ArithmeticFunction.moebius r : ℤ) : ℂ) else 0) ≠ 0 →
      (2 : ℝ) ^ j ≤ (r : ℝ) ∧ (r : ℝ) < 2 * 2 ^ j) := by
  constructor
  · split_ifs
    · rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · simp
  · intro h
    by_contra hc
    exact h ((ite_eq_right_iff.mpr (fun h' => absurd h'.2 hc)))

/-
Numerics. Lemma 3.2 asks y at least x^(1/2), met as H is at least Y^(2/3 + eta),
and L^B at most M at most y x^(-1/2) L^(-B) for the block M = 2^j: with x = Y/4
the paper bound is 2 H Y^(-1/2) (log x)^(-B), at least H Y^(-1/2) L^(-B); with
x = Y/2 it is sqrt 2 times that. The range of j is nonempty for large X since
H Y^(-1/2) at least Y^(1/6 + eta). b_k = 1 has |b_k| at most tau(k)^c.
Display 41 from the hypotheses on q, with B replaced by B - 1.
-/
/-- LEAF: P0088 Lemma 3.2 of page 10, with x = Y/4 and x = Y/2, y = H, c = 1,
L = log X, with the paper variable m the divisor r of the dyadic block 2^j at
most r below 2^(j+1), L^B below 2^j at most H Y^(-1/2) L^(-B), coefficient
a_r with |a_r| at most 1, and b_k = 1 for the cofactor k. Class HARD. -/
theorem leaf_lemma32_window_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j →
        (2 : ℝ) ^ j ≤ H / Real.sqrt (windowY X ε) / Real.log X ^ B →
        ∀ b : ℕ → ℂ, (∀ r : ℕ, ‖b r‖ ≤ 1) →
        (∀ r : ℕ, b r ≠ 0 → (2 : ℝ) ^ j ≤ (r : ℝ) ∧ (r : ℝ) < 2 * 2 ^ j) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ r ∈ m.divisors, b r) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Assembly: the exact statement of `leaf_case2_F2085`. -/
theorem leaf_case2_F2085_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        ∀ j : ℕ, Real.log X ^ B < (2 : ℝ) ^ j →
        (2 : ℝ) ^ j ≤ H / Real.sqrt (windowY X ε) / Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := leaf_lemma32_window_F2085 A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' η hη => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε' η hη
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hlow hup α q a hcop hq1 hq2 hdio z _ j hj hj'
  simp only [case2_coeff_F2085 z j]
  exact k X H hX hlow hup α q a hcop hq1 hq2 hdio j hj hj' _
    (fun r => (case2_coeff_bound_F2085 z j r).1)
    (fun r hr => (case2_coeff_bound_F2085 z j r).2 hr)

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_case2_F2085 := leaf_case2_F2085_split

end LeanLab.KumchevLiu2007.F2085
