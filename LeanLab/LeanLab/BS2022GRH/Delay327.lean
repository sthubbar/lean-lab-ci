/- AI wrote this Lean code for CODEX task327. Goldbach is open.
Finite integrals for the individual delay terms in the supplied source split.
BJS arXiv 2207.09452v6 pp. 6 to 8.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Decomp327a

namespace LeanLab.BS2022GRH.Delay327
open Real Finset Classical Decomp327a
noncomputable section

/-- Compact support turns the delay recurrence into a finite interval integral.
BJS p. 8 before display 21. The upper endpoint is n plus four because
this recurrence defines the term with index n plus two. -/
theorem delayTerm_window (n : ℕ) (s : ℝ)
    (hs : (if (n + 2) % 2 = 1 then max s 3 else s) ≤ (n : ℝ) + 4) :
    delayTerm (n + 2) s =
      (∫ t in (if (n + 2) % 2 = 1 then max s 3 else s)..((n : ℝ) + 4),
        delayTerm (n + 1) (t - 1)) / s := by
  rw [delayTerm, intervalIntegral.integral_of_le hs]
  congr 1
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self
  intro t ht
  have hlo := Set.mem_Ioi.mp ht.1
  have hhi : (n : ℝ) + 4 < t := by
    by_contra h
    apply ht.2
    exact ⟨hlo, le_of_not_gt h⟩
  apply delayTerm_eq_zero_of_endpoint
  push_cast
  linarith

/-- The second delay term is the elementary formula printed in the paper.
BJS p. 7 display 19, for two at most s at most four. -/
theorem delayTerm_two_formula (s : ℝ) (hs : 2 ≤ s) (ht : s ≤ 4) :
    delayTerm 2 s = (s - 3 * log (s - 1) + 3 * log 3 - 4) / s := by
  have hw := delayTerm_window 0 s (by simpa using ht)
  norm_num only at hw
  simp only [ite_false] at hw
  rw [hw]
  have heq : (∫ t in s..4, delayTerm 1 (t - 1)) =
      ∫ t in s..4, (4 - t) / (t - 1) := by
    apply intervalIntegral.integral_congr
    intro t hmem
    rw [Set.uIcc_of_le ht] at hmem
    change max (3 - (t - 1)) 0 / (t - 1) = (4 - t) / (t - 1)
    rw [max_eq_left (by linarith [hmem.2] : 0 ≤ 3 - (t - 1))]
    congr 1
    ring
  rw [heq]
  have hd (t : ℝ) (hmem : t ∈ Set.uIcc s 4) :
      HasDerivAt (fun t : ℝ => 3 * log (t - 1) - t) ((4 - t) / (t - 1)) t := by
    rw [Set.uIcc_of_le ht] at hmem
    have hne : t - 1 ≠ 0 := by linarith [hmem.1]
    have hlog := ((hasDerivAt_id t).sub_const 1).log hne
    have hf : HasDerivAt (fun x : ℝ => 3 * log (x - 1) - x)
        (3 * (1 / (t - 1)) - 1) t := by
      simpa only [id_eq, Pi.sub_def] using (hlog.const_mul 3).sub (hasDerivAt_id t)
    convert hf using 1 <;> field_simp <;> ring
  have hc : ContinuousOn (fun t : ℝ => (4 - t) / (t - 1)) (Set.uIcc s 4) := by
    apply ContinuousOn.div (continuous_const.sub continuous_id).continuousOn
      (continuous_id.sub continuous_const).continuousOn
    intro t hmem
    rw [Set.uIcc_of_le ht] at hmem
    change t - 1 ≠ 0
    linarith [hmem.1]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [hi]
  norm_num
  ring

#print axioms delayTerm_window
#print axioms delayTerm_two_formula

end
end LeanLab.BS2022GRH.Delay327
