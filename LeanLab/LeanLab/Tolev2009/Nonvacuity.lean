/-
AI wrote this Lean code. Codex task45.
Binary Goldbach is open.
Source: Tolev 2009, https://arxiv.org/abs/0902.2669.
The exact source pages and plain math twins are in STATEMENTS.md.
-/
import LeanLab.Tolev2009.MinorArcBound
import LeanLab.Tolev2009.SupremumAudit

open Finset Real MeasureTheory

namespace LeanLab.Tolev2009.Nonvacuity

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16 LeanLab.Tolev2009.Displays19to20
open LeanLab.Tolev2009.Dyadic

/-- A nonzero bounded third modulus weight. -/
def unitWeight (k : ℕ) : ℝ := if k = 1 then 1 else 0

theorem unitWeight_bounded : ∀ k, |unitWeight k| ≤ 1 := indicator_bounded 1

/-- At Q zero the major arc set is empty. -/
theorem majorArcs_zero (τ : ℝ) : majorArcs 0 τ = ∅ := by
  ext α
  simp [majorArcs]

/-- With empty major arcs, Rm is the full weighted prime representation count. -/
theorem Rm_zero_Q (τ : ℝ) (k l : Fin 3 → ℕ) (N : ℕ) : Rm 0 τ k l N = R k l N := by
  simp only [Rm, majorArcs_zero, Set.compl_empty, Set.indicator_univ]
  rw [show (1 : ℝ) - 1 / τ = -1 / τ + 1 by ring, integral_integrand, Complex.ofReal_re]

/-- The singleton modulus block has a strictly positive instance for the actual prime sums. -/
theorem singleton_block_pos : 0 < V 0 1 unitWeight 1 1 7 0 0 := by
  have hR : 0 < R ![1, 1, 1] ![0, 0, 1] 7 :=
    R_pos_of_rep (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (show 2 % 1 = 0 % 1 by norm_num) (show 2 % 1 = 0 % 1 by norm_num)
      (show 3 % 1 = 1 % 1 by norm_num)
  let g := fun l₁ l₂ => |∑ k₃ ∈ (Icc 1 1).filter (fun k₃ => Nat.Coprime k₃ 1),
    unitWeight k₃ * Rm 0 1 ![1, 1, k₃] ![l₁, l₂, 1] 7|
  have hmem : 0 ∈ residues 1 := by norm_num [residues]
  have hmax := le_iSup2 (residues 1) (residues 1) g (fun _ _ => abs_nonneg _) hmem hmem
  have hg : 0 < g 0 0 := by
    simpa [g, unitWeight, Rm_zero_Q, abs_of_nonneg (R_nonneg _ _ _)] using hR
  simpa only [V, block, sum_singleton, innerF] using hg.trans_le hmax

/-- The logarithmic large N hypothesis has a concrete small instance. -/
theorem log_seven_ge_one : 1 ≤ Real.log (7 : ℝ) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

/-- The cited pointwise display12 assumptions also have a nonzero weight instance.
This is not a witness to the uniform cited input. -/
theorem display12_nonzero_instance : ∃ cSup : ℝ, 0 ≤ cSup ∧
    Display12 (10 ^ 4) cSup 17 0 1 unitWeight 1 1 7 ∧ unitWeight 1 = 1 := by
  let L := Real.log (7 : ℝ)
  let x : ℝ := 350 - 4 * (10 ^ 4 : ℝ)
  let c : ℝ := Real.sqrt 17 * L ^ (10 : ℕ) / L ^ x
  have hL : 1 ≤ L := log_seven_ge_one
  have hL0 : 0 < L := by linarith
  have hpow : L ^ x ≠ 0 := (Real.rpow_pos_of_pos hL0 x).ne'
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  refine ⟨c, hc, ⟨?_, ?_⟩, by norm_num [unitWeight]⟩
  · intro α _ _
    have hb := SupremumAudit.coarse_sup unitWeight 1 1 7 unitWeight_bounded (by norm_num)
      (by norm_num) log_seven_ge_one α
    convert hb using 1
    dsimp only [c, x, L]
    field_simp
    ring
  · exact L2Bound.display12_L2 unitWeight 1 1 7 unitWeight_bounded (by norm_num)
      (by norm_num) log_seven_ge_one

end LeanLab.Tolev2009.Nonvacuity
