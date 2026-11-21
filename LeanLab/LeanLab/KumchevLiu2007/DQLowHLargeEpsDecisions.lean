/-
Cited wall decision for Task628.low_H_large_eps in LargeEpsilon628.lean.
Verdict MISCUT: the leaf mixes a cited part with an unwritten part.
Cited part: P0088 page 8 Proposition 1 display 33, applied on pages 15 and 16
with Y = X ^ theta1 and H = Y ^ theta2, theta1 at least 7/12 plus a margin and
theta2 at least 2/3 plus a margin, gives page 16 display 53. When epsilon is
below 11/24 every H of the leaf has theta2 above 2/3 by a fixed margin.
Unwritten part: epsilon from 11/24 to 5/6 and theta2 below 2/3 plus a margin.
The paper never states it and the page 15 check of hypothesis A2.3 fails there.
No paper error is claimed. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.LargeEpsilon628

namespace LeanLab.KumchevLiu2007.DQLowHLargeEps

open Real Complex Filter LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- NAMED HYPOTHESIS, CITED. P0088 page 16 display 53, in the lab's count form.
Source: Kumchev and Liu 2007, page 8 Proposition 1 display 33, with B at least
B0 of A, applied on page 16 after the page 15 verification of hypotheses A1.2,
A2.2 and A2.3, for Y = X ^ theta1 and H = Y ^ theta2 of page 4, under page 16
line before display 53: theta1 at least 7/12 plus epsilon over 2 and theta2 at
least 2/3 plus epsilon. Here the Y margin is the window parameter eps and the H
margin eta is a second fixed positive constant; the paper's epsilon is the
smaller of the two. The count form is display 33 plus the finite Chebyshev
step, as in Task516a.eq53_prop1. Y at most X is eps at most 5/6. -/
def Display53Theta : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 5 / 6 →
    ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- UNWRITTEN RESIDUE, OPEN, not a cited result. Page 16 display 53 for epsilon
from 11/24 to 5/6 and H below Y ^ (2/3 + eta) for some margin eta. P0088 does
not state this range: page 15 needs theta2 at least 2/3 plus epsilon for
hypothesis A2.3, and the recorded literature search of burst 20261117 found no
almost all result in this range. It is the weakest form the split needs: one
margin eta per B and epsilon suffices. -/
def LowHResidue : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ,
    11 / 24 ≤ ε → ε ≤ 5 / 6 → ∃ η : ℝ, 0 < η ∧
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (1 - ε) < H → H ≤ X → H ≤ windowY X ε →
        H < X ^ (7 / 18 + ε) → H < windowY X ε ^ (2 / 3 + η) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- Page 4 parameters: Y ^ t is X ^ ((7/12 + eps/2) * t) for X at least 0. -/
theorem windowY_rpow (X ε t : ℝ) (hX : 0 ≤ X) :
    windowY X ε ^ t = X ^ ((7 / 12 + ε / 2) * t) := by
  unfold windowY
  rw [← Real.rpow_mul hX]

/-- Exponent arithmetic for the cited range: with eta equal to
(1 - eps)/(7/12 + eps/2) - 2/3, Y ^ (2/3 + eta) is exactly X ^ (1 - eps). -/
theorem theta_margin_exp (ε : ℝ) (hε : 0 < ε) :
    (7 / 12 + ε / 2) * (2 / 3 + ((1 - ε) / (7 / 12 + ε / 2) - 2 / 3)) = 1 - ε := by
  have h : (7 / 12 + ε / 2) ≠ 0 := by positivity
  field_simp
  ring

/-- The margin eta above is positive exactly when eps is below 11/24. -/
theorem theta_margin_pos (ε : ℝ) (hε : 0 < ε) (hε' : ε < 11 / 24) :
    0 < (1 - ε) / (7 / 12 + ε / 2) - 2 / 3 := by
  have h : 0 < 7 / 12 + ε / 2 := by positivity
  rw [sub_pos, lt_div_iff₀ h]
  linarith

/-- Twin of Task628.low_H_large_eps, the exact leaf statement, CONDITIONAL ON
Display53Theta, cited, and LowHResidue, unwritten and open. For eps below
11/24 the cited display 53 covers every H of the leaf; for eps from 11/24 to
5/6 the residue covers H below Y ^ (2/3 + eta) and display 53 the rest. -/
theorem low_H_large_eps_of_split (h53 : Display53Theta) (hres : LowHResidue)
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ,
      11 / 36 < ε → ε ≤ 5 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (1 - ε) < H → H ≤ X → H ≤ windowY X ε →
        H < X ^ (7 / 18 + ε) →
        (cntIoc (fun n => InH2 n ∧
          Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := h53 A hA
  obtain ⟨B2, hB2, h2⟩ := hres A hA
  refine ⟨max B1 B2, hB1.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hεlo hεhi
  have hB1' : B1 ≤ B := (le_max_left _ _).trans hB
  have hB2' : B2 ≤ B := (le_max_right _ _).trans hB
  have hε : 0 < ε := by linarith
  by_cases hsmall : ε < 11 / 24
  · obtain ⟨C, X0, hC, hX0, h⟩ :=
      h1 B hB1' ε hε hεhi _ (theta_margin_pos ε hε hsmall)
    refine ⟨C, X0, hC, hX0, ?_⟩
    intro X H hX hlo _ hHY _
    have hX' : 0 ≤ X := by linarith
    apply h X H hX _ hHY
    rw [windowY_rpow X ε _ hX', theta_margin_exp ε hε]
    exact hlo.le
  · obtain ⟨η, hη, C1, X1, hC1, hX1, hr⟩ := h2 B hB2' ε (not_lt.mp hsmall) hεhi
    obtain ⟨C2, X2, hC2, hX2, h⟩ := h1 B hB1' ε hε hεhi η hη
    refine ⟨max C1 C2, max X1 X2, hC1.trans_le (le_max_left _ _),
      hX1.trans (le_max_left _ _), ?_⟩
    intro X H hX hlo hHX hHY hH718
    have hx1 : X1 ≤ X := (le_max_left _ _).trans hX
    have hx2 : X2 ≤ X := (le_max_right _ _).trans hX
    have hX' : 1 < X := by linarith
    have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos hX') _
    have hH : 0 ≤ H := (Real.rpow_nonneg (by linarith) _).trans hlo.le
    by_cases hθ : H < windowY X ε ^ (2 / 3 + η)
    · exact (hr X H hx1 hlo hHX hHY hH718 hθ).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hH) hLA.le)
    · exact (h X H hx2 (not_lt.mp hθ) hHY).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hH) hLA.le)

/-- Twin check: the conditional assembly has exactly the type of the leaf. -/
example (h53 : Display53Theta) (hres : LowHResidue) (A : ℝ) (hA : 0 < A) :
    type_of% (Task628.low_H_large_eps A hA) :=
  low_H_large_eps_of_split h53 hres A hA

/-- Vacuity check for the residue: at eps = 5/6 the residue range is nonempty,
X = 2 ^ 36 and H = 2 ^ 7 lie strictly between X ^ (1/6) and Y ^ (2/3). -/
theorem residue_range_nonempty :
    ∃ X H : ℝ, (2 : ℝ) ≤ X ∧ X ^ (1 - (5 / 6 : ℝ)) < H ∧ H ≤ X ∧
      H ≤ windowY X (5 / 6) ∧ H < X ^ (7 / 18 + (5 / 6 : ℝ)) ∧
      H < windowY X (5 / 6) ^ (2 / 3 : ℝ) := by
  refine ⟨(2 : ℝ) ^ (36 : ℝ), (2 : ℝ) ^ (7 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ (36 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · rw [← Real.rpow_mul (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · unfold windowY
    rw [← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · rw [← Real.rpow_mul (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  · rw [windowY_rpow _ _ _ (by positivity), ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

end LeanLab.KumchevLiu2007.DQLowHLargeEps

#print axioms LeanLab.KumchevLiu2007.DQLowHLargeEps.windowY_rpow
#print axioms LeanLab.KumchevLiu2007.DQLowHLargeEps.theta_margin_exp
#print axioms LeanLab.KumchevLiu2007.DQLowHLargeEps.theta_margin_pos
#print axioms LeanLab.KumchevLiu2007.DQLowHLargeEps.low_H_large_eps_of_split
#print axioms LeanLab.KumchevLiu2007.DQLowHLargeEps.residue_range_nonempty
