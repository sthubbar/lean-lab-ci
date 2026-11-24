/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`F2085.leaf_case1_F2085`, ROUTE BURST S98 burst-20261122, Case 1 of the proof
of Lemma 3.4 on page 11 with x = Y, y = H, (m, k) = (1, m).

* `case1_coeff_F2085`: the block coefficient of display 42 is the divisor sum
  of b_r = mu(r) on z smooth r in the block 2^j at most r below 2^(j+1).
  Proved.
* `leaf_lemma31_window_F2085`: Lemma 3.1 of page 9 for such b_r, |b_r| at most
  1, support r below 2 L^B. LEAF, HARD.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_first_sum_F2085

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- Proved. The block coefficient of display 42, P0088 page 11, as a divisor sum
of the coefficient b_r = mu(r) on z smooth r in the dyadic block. -/
theorem case1_coeff_F2085 (z : ℝ) (j m : ℕ) :
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
theorem case1_coeff_bound_F2085 (z : ℝ) (j r : ℕ) :
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
Numerics. Lemma 3.1 asks y at least x^(1/2): H at least Y^(2/3 + eta) is at
least Y^(1/2) once Y at least 1. Support: r below 2^(j+1) at most 2 L^B, far
below x^(1/4) L^(-B) for x = Y/4 and Y/2, since Y = X^(7/12 + eps/2) and L =
log X. The window Y/4 to Y is the two windows x to 2x. Display 41 from the
hypotheses on q, with log x at most L, as B is replaced by B - 1.
-/
/-- LEAF: P0088 Lemma 3.1 of page 9, with x = Y/4 and x = Y/2, y = H, c = 1,
L = log X, for a type I coefficient b_r with |b_r| at most 1 supported on one
dyadic block 2^j at most r below 2^(j+1) with 2^j at most L^B, so R at most
x^(1/4) L^(-B); the sum over m with r dividing m is the sum over m = rk of the
paper. Class HARD. -/
theorem leaf_lemma31_window_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.log X ^ B →
        ∀ b : ℕ → ℂ, (∀ r : ℕ, ‖b r‖ ≤ 1) →
        (∀ r : ℕ, b r ≠ 0 → (2 : ℝ) ^ j ≤ (r : ℝ) ∧ (r : ℝ) < 2 * 2 ^ j) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ r ∈ m.divisors, b r) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- Assembly: the exact statement of `leaf_case1_F2085`. -/
theorem leaf_case1_F2085_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        ∀ j : ℕ, (2 : ℝ) ^ j ≤ Real.log X ^ B →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (m.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := leaf_lemma31_window_F2085 A hA
  refine ⟨B0, hB0, fun B hB ε hε hε' η hη => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := h B hB ε hε hε' η hη
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hlow hup α q a hcop hq1 hq2 hdio z _ j hj
  simp only [case1_coeff_F2085 z j]
  exact k X H hX hlow hup α q a hcop hq1 hq2 hdio j hj _
    (fun r => (case1_coeff_bound_F2085 z j r).1)
    (fun r hr => (case1_coeff_bound_F2085 z j r).2 hr)

/-- The split statement is character for character the parent leaf. -/
example : type_of% @leaf_case1_F2085 := leaf_case1_F2085_split

end LeanLab.KumchevLiu2007.F2085
