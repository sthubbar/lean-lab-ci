/-
Split of `leaf_case3_block` of `LeanLab.KumchevLiu2007.Lemma34FirstSumCases`,
Case 3 of the proof of Lemma 3.4 of Kumchev and Liu 2007, P0088 page 12, on the
left half [Y / 4, Y / 2] of the window, with x = Y / 4, y = H and M = 1.

Lemma 3.4 on page 11 assumes y ≤ x. The lab statement keeps H up to
X^(1 - eps), above the paper's range. In the part H ≥ Y L^B / 2 of that range
the block of Case 3 is empty: a divisor d of a square root m < Y^(1/2) is at
most m, while d ≥ 2^j > H x^(-1/2) L^(-B) ≥ Y^(1/2). That part is PROVED here
in `case3_block_large_H`. The remaining part, H < Y L^B / 2, which contains the
paper's range y ≤ x, is the LEAF `leaf_case3_block_core`, the paper's Case 3
argument: the factorisation d = d1 p p' d2, Lemma 3.3 cited to Kumchev 2006
Lemma 2.7, and Lemma 3.2 cited to Liu and Zhan 1997.

`case3_block_of_core` proves the statement of `leaf_case3_block` from the
LEAF, with no sorry of its own.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum

namespace LeanLab.KumchevLiu2007.Eq33RouteD.Case3BlockLeft1123

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a LeanLab.KumchevLiu2007.Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 12, Case 3 of the proof of Lemma 3.4 with M = 1, on the
left half [Y / 4, Y / 2], restricted to H < Y L^B / 2, the range where the
block can be nonempty: the dyadic block 2^j ≤ d < 2^(j+1) of display 42 with
2^j above V = y x^(-1/2) L^(-B), x = Y / 4, y = H. The paper writes
d = d1 p p' d2 with L^B ≤ d1 p < V ≤ d1 p p', removes the side conditions by
Lemma 3.3, cited to Kumchev 2006 Lemma 2.7, and applies Lemma 3.2, cited to
Liu and Zhan 1997 Lemma 3.2. Class HARD, cited input. -/
theorem leaf_case3_block_core (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ B / 2 →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, outside the paper's range
y ≤ x: for H ≥ Y L^B / 2 and 2^j > H (Y / 4)^(-1/2) L^(-B), every block weight
vanishes on the square root window, since a divisor of m is at most
m < Y^(1/2) ≤ H (Y / 4)^(-1/2) L^(-B). -/
theorem case3_block_large_H (X ε B H z α : ℝ) (j : ℕ) (hY : 0 < windowY X ε)
    (hLB : 0 < Real.log X ^ B) (hH : windowY X ε * Real.log X ^ B / 2 ≤ H)
    (hj : H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B < (2 : ℝ) ^ j) (A C : ℝ)
    (hC : 0 < C) (hA : 0 ≤ Real.log X ^ A) :
    (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
      ‖∑ n ∈ (squareWindow (windowY X ε)).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
        (∑ d ∈ (n.divisors.filter
            (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
        C * H ^ 2 / Real.log X ^ A := by
  set Y := windowY X ε with hYdef
  have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hs4 : Real.sqrt (Y / 4) = Real.sqrt Y / 2 := by
    rw [show Y / 4 = Y * (1 / 2) ^ 2 by ring, Real.sqrt_mul hY.le,
      Real.sqrt_sq (by norm_num)]
    ring
  have hroot : Real.sqrt Y ≤ H / Real.sqrt (Y / 4) / Real.log X ^ B := by
    rw [hs4, le_div_iff₀ hLB, le_div_iff₀ (by positivity)]
    have := Real.mul_self_sqrt hY.le
    nlinarith
  have hzero : ∀ t : ℝ,
      ‖∑ n ∈ (squareWindow Y).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
        (∑ d ∈ (n.divisors.filter
            (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
            (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
          fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 = 0 := by
    intro t
    rw [Finset.sum_eq_zero, norm_zero]
    · norm_num
    intro n hn
    rw [Finset.sum_eq_zero, zero_mul]
    intro d hd
    exfalso
    obtain ⟨hn1, -⟩ := Finset.mem_filter.mp hn
    obtain ⟨-, hnlo, hnhi⟩ := Finset.mem_filter.mp hn1
    obtain ⟨hd1, hd2, -⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdn, hn0⟩ := Nat.mem_divisors.mp (Finset.mem_filter.mp hd1).1
    have hdle : (d : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn
    linarith
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t _ => hzero t)]
  simp only [intervalIntegral.integral_zero]
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  positivity

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4 on the left half: the
statement of `leaf_case3_block`, from `leaf_case3_block_core` for
H < Y L^B / 2 and from `case3_block_large_H` otherwise.
CONDITIONAL ON leaf_case3_block_core. -/
theorem case3_block_of_core (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, hcore⟩ := leaf_case3_block_core A hA
  refine ⟨B0, hB0, fun B hB ε hε => ?_⟩
  obtain ⟨C, X0, hC, hX0, k⟩ := hcore B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z hz2 hz j hj
  by_cases hsmall : H < windowY X ε * Real.log X ^ B / 2
  · exact k X H hX hlow hhigh hsmall α q v hcop hqP hqQ hclose z hz2 hz j hj
  · have hX0' : 0 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    exact case3_block_large_H X ε B H z α j
      (by unfold windowY; exact Real.rpow_pos_of_pos hX0' _)
      (Real.rpow_pos_of_pos hL B) (not_lt.mp hsmall) hj A C hC
      (Real.rpow_pos_of_pos hL A).le

end LeanLab.KumchevLiu2007.Eq33RouteD.Case3BlockLeft1123

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3BlockLeft1123.leaf_case3_block_core
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3BlockLeft1123.case3_block_large_H
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.Case3BlockLeft1123.case3_block_of_core
