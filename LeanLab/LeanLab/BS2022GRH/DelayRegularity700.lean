/- AI wrote this Lean code for CODEX task700. Goldbach is open.
Continuity of the individual delay terms and their series.
BJS arXiv 2207.09452v6 p. 6 displays 13 to 17,
Nathanson 1996 pp. 250 and 251 Theorem 9.4.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Delay327
import LeanLab.BS2022GRH.DelayTerms700

namespace LeanLab.BS2022GRH.DelayRegularity700
open Real Set MeasureTheory Decomp327a Delay327 Delay700 DelayTerms700
noncomputable section

/-- A clamped finite interval represents the delay recurrence at every argument. -/
theorem delayTerm_clamped_window (n : ℕ) (s : ℝ) :
    delayTerm (n+2) s =
      (∫ t in min (if (n+2)%2=1 then max s 3 else s) ((n : ℝ)+4)..((n : ℝ)+4),
        delayTerm (n+1) (t-1)) / s := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  let a := if (n+2)%2=1 then max s 3 else s
  by_cases ha : a ≤ (n : ℝ)+4
  · rw [min_eq_left ha]
    exact delayTerm_window n s ha
  · rw [min_eq_right (le_of_not_ge ha), intervalIntegral.integral_same, zero_div]
    apply delayTerm_eq_zero_of_endpoint
    dsimp [a] at ha
    split_ifs at ha with h
    · have hs : (n : ℝ)+4 < s := by
        have hn : (3 : ℝ) ≤ (n : ℝ)+4 := by linarith
        exact (lt_max_iff.mp (lt_of_not_ge ha)).resolve_right (not_lt_of_ge hn)
      push_cast
      linarith
    · push_cast
      linarith

/-- Each delay term is continuous on its parity domain. -/
theorem continuousOn_delayTerm (n : ℕ) :
    ContinuousOn (delayTerm n) (Ici (if n%2=1 then (1 : ℝ) else 2)) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [delayTerm] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
  | one =>
      norm_num only
      apply ContinuousOn.div
      · exact ((continuous_const.sub continuous_id).max continuous_const).continuousOn
      · exact continuous_id.continuousOn
      · intro s hs
        have hs' : 1 ≤ s := hs
        change s ≠ 0
        linarith
  | more n ih0 ih1 =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      let a : ℝ := if (n+2)%2=1 then 3 else 2
      let b : ℝ := (n : ℝ)+4
      let d : ℝ := if (n+2)%2=1 then 1 else 2
      let c : ℝ → ℝ := fun s => min (if (n+2)%2=1 then max s 3 else s) b
      have hab : a ≤ b := by dsimp [a,b]; split_ifs <;> linarith
      have hc : Continuous c := by dsimp [c]; split_ifs <;> fun_prop
      have hcm : MapsTo c (Ici d) (uIcc a b) := by
        intro s hs
        rw [uIcc_of_le hab]
        dsimp [c,a,b,d] at hs ⊢
        by_cases h : (n+2)%2=1
        · simp only [ite_eq_left h] at hs ⊢
          exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
        · simp only [ite_eq_right h] at hs ⊢
          exact ⟨le_min hs (by linarith), min_le_right _ _⟩
      have hprev : ContinuousOn (fun t : ℝ => delayTerm (n+1) (t-1)) (Icc a b) := by
        apply ih1.comp (continuous_id.sub continuous_const).continuousOn
        intro t ht
        have ht' : a ≤ t := ht.1
        dsimp [a] at ht'
        by_cases h : (n+2)%2=1
        · rw [ite_eq_left h] at ht'
          have hp : (n+1)%2 ≠ 1 := by omega
          simp only [ite_eq_right hp, mem_Ici, Pi.sub_apply, id_eq]
          linarith
        · rw [ite_eq_right h] at ht'
          have hp : (n+1)%2=1 := by omega
          simp only [ite_eq_left hp, mem_Ici, Pi.sub_apply, id_eq]
          linarith
      have hi : IntegrableOn (fun t : ℝ => delayTerm (n+1) (t-1)) (uIcc a b) := by
        rw [uIcc_of_le hab]
        exact hprev.integrableOn_Icc
      have hp := intervalIntegral.continuousOn_primitive_interval_left hi
      have heq : EqOn (delayTerm (n+2))
          (fun s => (∫ t in c s..b, delayTerm (n+1) (t-1))/s) (Ici d) := by
        intro s _
        exact delayTerm_clamped_window n s
      apply ContinuousOn.congr ((hp.comp hc.continuousOn hcm).div continuous_id.continuousOn ?_) heq
      intro s hs
      have hs' : d ≤ s := hs
      have hd : 0 < d := by dsimp [d]; split_ifs <;> norm_num
      change s ≠ 0
      linarith

/-- The auxiliary weight is at most one on all delay domains. -/
theorem weight_le_one (s : ℝ) (hs : 1 ≤ s) : weight s ≤ 1 := by
  have hh := weight_shift_le (s+1) (by linarith)
  have he1 : s+1-1=s := by ring
  have he2 : 1-(s+1) = -s := by ring
  rw [he1, he2] at hh
  exact hh.trans (exp_le_one_iff.mpr (by linarith))

/-- The odd delay series is continuous on its full domain. -/
theorem continuousOn_odd_tsum :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if n%2=1 then delayTerm n s else 0) (Ici 1) := by
  apply continuousOn_tsum (u := fun n : ℕ => 4 * exp 3 * (99/100 : ℝ)^n)
  · intro n
    by_cases h : n%2=1
    · simpa [h] using continuousOn_delayTerm n
    · simpa [h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)).mul_left _
  · intro n s hs
    have hs' : 1 ≤ s := hs
    by_cases h : n%2=1
    · rw [ite_eq_left h, Real.norm_of_nonneg (delayTerm_nonneg n s (by simpa [h] using hs'))]
      exact (delayTerm_geometric n s (by simpa [h] using hs')).trans
        (mul_le_of_le_one_right (by positivity) (weight_le_one s hs'))
    · rw [ite_eq_right h, norm_zero]
      positivity

/-- The positive even delay series is continuous on its full domain. -/
theorem continuousOn_even_tsum :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if 0<n ∧ n%2=0 then delayTerm n s else 0) (Ici 2) := by
  apply continuousOn_tsum (u := fun n : ℕ => 4 * exp 3 * (99/100 : ℝ)^n)
  · intro n
    by_cases h : 0<n ∧ n%2=0
    · have ho : n%2 ≠ 1 := by omega
      simpa [h, ho] using continuousOn_delayTerm n
    · simpa [h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99/100)
      (by norm_num)).mul_left _
  · intro n s hs
    have hs' : 2 ≤ s := hs
    by_cases h : 0<n ∧ n%2=0
    · have ho : n%2 ≠ 1 := by omega
      rw [ite_eq_left h, Real.norm_of_nonneg (delayTerm_nonneg n s (by simpa [ho] using hs'))]
      exact (delayTerm_geometric n s (by simpa [ho] using hs')).trans
        (mul_le_of_le_one_right (by positivity) (weight_le_one s (by linarith)))
    · rw [ite_eq_right h, norm_zero]
      positivity

end
end LeanLab.BS2022GRH.DelayRegularity700

#print axioms LeanLab.BS2022GRH.DelayRegularity700.delayTerm_clamped_window
#print axioms LeanLab.BS2022GRH.DelayRegularity700.continuousOn_delayTerm

#print axioms LeanLab.BS2022GRH.DelayRegularity700.weight_le_one
#print axioms LeanLab.BS2022GRH.DelayRegularity700.continuousOn_odd_tsum
#print axioms LeanLab.BS2022GRH.DelayRegularity700.continuousOn_even_tsum
