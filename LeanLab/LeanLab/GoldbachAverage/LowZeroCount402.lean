import LeanLab.PNTPort.Selberg.Count

/-!
BHMS, arXiv 1704.06103v2 page 18, the count of low ordinates after Lemma 6.
This bridge uses the existing unconditional PNTPort head count.
The factor ninety is a conservative derived constant.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.LowZeroCount402
open Finset
open LeanLab.PNTPort.Selberg

/-- The low ordinate multiplicity count in the last low zero display on BHMS page 18.
The statement is over every finite set of genuine nontrivial zeros. -/
theorem low_ordinate_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ x / h) →
      (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C * (x / h) * Real.log x := by
  obtain ⟨H, hH, hcount⟩ := head_count
  refine ⟨90 * H, by positivity, ?_⟩
  intro x h hx hh hhx S hS
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hT1 : 1 ≤ x / h := (le_div_iff₀ hh0).mpr (by simpa using hhx)
  have hT0 : 0 < x / h := by positivity
  have hTx : x / h ≤ x := div_le_self hx0.le (by linarith)
  have hc := hcount (6 * (x / h)) (by linarith) S (by
    intro ρ hρ
    obtain ⟨hz, hre0, hre1, him⟩ := hS ρ hρ
    have hn := norm_le_of_NZ (show NZ ρ from ⟨hz, hre0, hre1⟩)
    exact ⟨⟨hz, hre0, hre1⟩, by linarith⟩)
  have hlogx : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hlog : Real.log (6 * (x / h)) + 2 ≤ 15 * Real.log x := by
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hT0.ne']
    have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    have hT := Real.log_le_log hT0 hTx
    linarith
  change (∑ ρ ∈ S, mz ρ) ≤ _
  calc (∑ ρ ∈ S, mz ρ) ≤ H * (6 * (x / h)) * (Real.log (6 * (x / h)) + 2) := hc
    _ ≤ H * (6 * (x / h)) * (15 * Real.log x) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

end LeanLab.GoldbachAverage.LowZeroCount402
