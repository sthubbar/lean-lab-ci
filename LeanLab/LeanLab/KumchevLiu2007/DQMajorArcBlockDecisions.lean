/-
CITED WALL decision for Task628.major_arc_block, burst 20261120, CLOUD-cited-major_arc_block.
P0088, Kumchev and Liu, arXiv 0801.0130, page 7 display 28, with the page 15
weights f1 = 1/log u and f2 before display 53, z0 = Y^(1/4) P^(-2) of display 34.

DECISION: NAMED HYPOTHESIS. Display 28 is the pointwise major arc estimate
  integral over M of S1 S2 e(-alpha n) = S2(n,P) I(n) + O(Y^(1/2) P^(-1/2+eta)),
derived on pages 5 to 7 from displays 20, 24, 26 and 27. Those rest on the
hypotheses (A1.2) and (A2.2), which page 15 asserts for the primes and for
lambda0 only by reference to "the same methods as Huxley's theorem on primes in
short intervals"; no proof is printed. Squaring and taking B with
B(1 - 2 eta) at least A gives exactly the leaf shape below. The leaf restricts
H to at most Y P^(-4), which is the range where the delta edge term in the
Gallagher bound before display 20 is at most P^(-4), and H at least
X^(7/18+eps) P^(-4), which keeps the major arcs inside |beta| at most
Y^(-1/2)/4 where display 22 for T2 is valid.

The file adds the named Prop, the exact leaf from it, and the conditional
chain up to the written Theorem 1 of Thm1Written, taking the
rough_block_bulk statement as an explicit second hypothesis.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Block628
import LeanLab.KumchevLiu2007.Thm1Written

namespace LeanLab.KumchevLiu2007.DQMajorArcBlock

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- NAMED HYPOTHESIS, cited analytic estimate. P0088 page 7 display 28,
squared, with lambda1 the primes on I1 = [X - Y, X) and lambda2 = lambda0 of
page 8 display 34 on I2 = [Y^(1/2)/2, Y^(1/2)), weights of page 15, P = L^B,
Q = H/P as in page 4 display 14. Its proof on pages 5 to 7 uses displays 20,
24, 26, 27 and the hypotheses (A1.2), (A2.2), asserted on page 15 by Huxley
type methods. Word for word the body of `Task628.major_arc_block`. -/
def MajorArcBlockHyp : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A

/-- The exact statement of the leaf `Task628.major_arc_block` from the named
hypothesis. CONDITIONAL ON MajorArcBlockHyp; no sorry. -/
theorem major_arc_block_of_hyp (h : MajorArcBlockHyp) (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A :=
  h A hA

/-- The sealed leaf implies the hypothesis, so the hypothesis asks no more
than the leaf did. CONDITIONAL ON Task628.major_arc_block, an open LEAF. -/
theorem hyp_of_leaf : MajorArcBlockHyp := fun A hA => major_arc_block A hA

/-- Page 7 hypothesis (A2.3) with the initial interval, the statement of
`Task628.rough_block_energy`, from the rough_block_bulk statement taken as a
hypothesis. Same proof as in BlockInputs628. CONDITIONAL ON hR. -/
theorem rough_block_energy_of_bulk
    (hR : ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X →
          X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
          H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
          ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
          (∫ t in (windowY X ε / 4)..windowY X ε,
            ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
              C * H ^ 2 / Real.log X ^ (A + 2))
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        ((∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) +
          ∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ (A + 2) := by
  obtain ⟨B0, hB0, hb⟩ := hR A hA
  refine ⟨max B0 (A + 2), hB0.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hb⟩ := hb B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨X1, hX1, hr⟩ := block_root_eventually B ε hε
  refine ⟨4 + C, max X0 X1, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hlo hhi α hα
  have hx0 : X0 ≤ X := (le_max_left _ _).trans hX
  have hx1 : X1 ≤ X := (le_max_right _ _).trans hX
  have hX3 : 3 ≤ X := hX1.trans hx1
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hB' : A + 2 ≤ 4 * B := by linarith [le_trans (le_max_right B0 (A + 2)) hB]
  have hi := block_initial_energy (α := α) hX3 hY (hr X H hx1 hlo) hB' hhi
  have hm := hb X H hx0 hlo hhi α hα
  calc _ ≤ 4 * H ^ 2 / Real.log X ^ (A + 2) + C * H ^ 2 / Real.log X ^ (A + 2) :=
        add_le_add hi hm
    _ = _ := by ring

/-- Page 8 display 33 on short translated blocks, the statement of
`Task628.weighted_block_mean_square`. Same proof as in Block628 with the two
inputs replaced by hypotheses. CONDITIONAL ON MajorArcBlockHyp and hR. -/
theorem weighted_block_mean_square_of_hyps (hM : MajorArcBlockHyp)
    (hR : ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X →
          X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
          H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
          ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
          (∫ t in (windowY X ε / 4)..windowY X ε,
            ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
              C * H ^ 2 / Real.log X ^ (A + 2))
    (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X X' H : ℝ,
        X0 ≤ X → X ≤ X' → X' ≤ X + windowY X ε →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∑ n ∈ intervalNumbers X' H, err53 X ε B n ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨B1, hB1, hm⟩ := hM A hA
  obtain ⟨B2, hB2, he⟩ := rough_block_energy_of_bulk hR A hA
  refine ⟨max B1 B2, hB1.trans_le (le_max_left _ _), ?_⟩
  intro B hB ε hε
  have hBpos : 0 < B := hB1.trans_le ((le_max_left _ _).trans hB)
  obtain ⟨C1, X1, hC1, hX1, hm⟩ := hm B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, he⟩ := he B ((le_max_right _ _).trans hB) ε hε
  obtain ⟨X3, hX3, hl⟩ := block_length_eventually B ε hε
  refine ⟨4 * C1 + 128 * π ^ 2 * C2, max (max X1 X2) X3, by positivity,
    hX1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X X' H hX hXX' _hX' hlo hhi
  have hx1 : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hx2 : X2 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hx3 : X3 ≤ X := (le_max_right _ _).trans hX
  have hX3' : 3 ≤ X := hX3.trans hx3
  have hX'0 : 0 ≤ X' := by linarith
  have hH2 : 2 ≤ H := hl X H hx3 hlo
  obtain ⟨_heps, hY1, hYX, hHX⟩ := block_window_parameters hX3' hBpos.le hε hlo hhi
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hc : ((intervalNumbers X' H).card : ℝ) ≤ 2 * H := by
    rw [Task556b.intervalNumbers_eq_Ioc hX'0]
    exact Task506aTask271a.interval_card_le hX'0 (by linarith)
  have hmajor : (∑ n ∈ intervalNumbers X' H,
      ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
        2 * C1 * H * windowY X ε / Real.log X ^ A := by
    calc
      _ ≤ ∑ _n ∈ intervalNumbers X' H, C1 * windowY X ε / Real.log X ^ A :=
        Finset.sum_le_sum fun n _ => hm X H hx1 hlo hhi n
      _ = ((intervalNumbers X' H).card : ℝ) *
          (C1 * windowY X ε / Real.log X ^ A) := by simp
      _ ≤ (2 * H) * (C1 * windowY X ε / Real.log X ^ A) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hminor := minor_block_of_complete_energy hX3' hX'0 (by linarith) hY1 hH2 hHX
    hC2.le (he X H hx2 hlo hhi)
  have hs := Task506aTask129b.mean_square_add (intervalNumbers X' H)
    (majorError X (windowY X ε) H (Real.log X ^ B))
    (minorCoefficient X (windowY X ε) H (Real.log X ^ B))
  have herr : ∀ n, err53 X ε B n =
      ‖majorError X (windowY X ε) H (Real.log X ^ B) n +
        minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ := by
    intro n
    unfold err53
    rw [Task556b.error_eq_major_add_minor X ε B H n]
  simp_rw [herr]
  calc _ ≤ _ := hs
    _ ≤ 2 * (2 * C1 * H * windowY X ε / Real.log X ^ A) +
        2 * (64 * π ^ 2 * C2 * H * windowY X ε / Real.log X ^ A) := by
      linarith
    _ = _ := by ring

/-- Page 8 display 33 in the written range, the named `Task129W.Eq33Hyp` of
Thm1Written, through the proved block covering of Eq33Window1117.
CONDITIONAL ON MajorArcBlockHyp and hR. -/
theorem eq33Hyp_of_hyps (hM : MajorArcBlockHyp)
    (hR : ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X →
          X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
          H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
          ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
          (∫ t in (windowY X ε / 4)..windowY X ε,
            ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
              C * H ^ 2 / Real.log X ^ (A + 2)) :
    Task129W.Eq33Hyp := by
  intro A hA
  exact Eq33Window1117.eq33_weighted_mean_square_of_blocks A hA
    (weighted_block_mean_square_of_hyps hM hR A hA)

/-- Theorem 1 of P0088 on the written range of page 16, the Prop
`Task129W.kumchev_liu_thm1_written`. CONDITIONAL ON MajorArcBlockHyp and hR,
the rough_block_bulk statement; no sorry in this proof. -/
theorem thm1_written_of_hyps (hM : MajorArcBlockHyp)
    (hR : ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X →
          X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
          H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
          ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
          (∫ t in (windowY X ε / 4)..windowY X ε,
            ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
              C * H ^ 2 / Real.log X ^ (A + 2)) :
    Task129W.kumchev_liu_thm1_written :=
  Task129W.thm1_written_of_eq33 (eq33Hyp_of_hyps hM hR)

end LeanLab.KumchevLiu2007.DQMajorArcBlock

#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.major_arc_block_of_hyp
#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.hyp_of_leaf
#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.rough_block_energy_of_bulk
#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.weighted_block_mean_square_of_hyps
#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.eq33Hyp_of_hyps
#print axioms LeanLab.KumchevLiu2007.DQMajorArcBlock.thm1_written_of_hyps
