/-
Split of `leaf_case3_block_right` along P0088 page 12, Case 3 of the proof
of Lemma 3.4: the Lemma 3.3 reduction to a bilinear form in v = p d1 with
L^B ≤ v ≤ V, then Lemma 3.2 with divisor bounded coefficients b_u.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_large_cutoff_right_half

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 10, Lemma 3.2, cited to Liu and Zhan 1997 Lemma 3.2,
with |a_m| ≤ 1 and |b_k| ≤ tau(k)^c as in the paper, lab form with
x = Y / 2, t over [Y / 2, Y], y = H, L^B ≤ M ≤ y x^(-1/2) L^(-B), m ~ M read
as M ≤ m < 2M. B0 may depend on A and c. Class HARD, cited type II. -/
theorem leaf_lemma32_tau_right (A : ℝ) (hA : 0 < A) (c : ℕ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) →
        (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ c) →
        ∀ M : ℝ, Real.log X ^ B ≤ M →
        M ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 12, Case 3 of Lemma 3.4: write d = d1 p p' d2 with
L^B ≤ d1 p < V ≤ d1 p p', remove p' < p, d ~ 2^j and d1 p p' ≥ V by
Lemma 3.3 at a cost L^c, split v = p d1 in [L^B, V] into dyadic blocks,
keep the worst block M. Here a_v is the coefficient of v, b_u that of
u = k p' d2 with |b_u| ≤ tau(u)^c. Class HARD. -/
theorem leaf_case3_lemma33_reduction_right :
    ∃ c : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B < (2 : ℝ) ^ j →
        ∃ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) ∧
          (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ c) ∧
          ∃ M : ℝ, Real.log X ^ B ≤ M ∧
            M ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * Real.log X ^ c *
          (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
  sorry

/-- `leaf_case3_block_right` from the two leaves above. -/
theorem leaf_case3_block_right_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨c, hR⟩ := leaf_case3_lemma33_reduction_right
  obtain ⟨B0, hB0, hT⟩ := leaf_lemma32_tau_right (A + c) (by positivity) c
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, hT'⟩ := hT B hB ε hε
  obtain ⟨C2, X2, hC2, hX2, hR'⟩ := hR B (lt_of_lt_of_le hB0 hB) ε hε
  refine ⟨C2 * C1, max X1 X2, by positivity, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z hz2 hzY j hj
  have hXX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hXX2 : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  obtain ⟨a, b, ha, hb, M, hM1, hM2, hred⟩ :=
    hR' X H hXX2 hlow hhigh α z hz2 hzY j hj
  have hbil := hT' X H hXX1 hlow hhigh α q v hcop hqP hqQ hclose a b ha hb M hM1 hM2
  refine hred.trans ?_
  have hLc : 0 ≤ C2 * Real.log X ^ c := by positivity
  calc C2 * Real.log X ^ c * _ ≤ C2 * Real.log X ^ c * (C1 * H ^ 2 / Real.log X ^ (A + c)) :=
        mul_le_mul_of_nonneg_left hbil hLc
    _ = C2 * C1 * H ^ 2 / Real.log X ^ A := by
        rw [Real.rpow_add hL, Real.rpow_natCast]
        have h1 : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL _
        have h2 : 0 < Real.log X ^ c := pow_pos hL _
        field_simp

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_case3_block_right_split
