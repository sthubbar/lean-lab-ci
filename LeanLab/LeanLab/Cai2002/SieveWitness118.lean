/-
P0044, pages 598 to 599. A local witness for the initial sieve equations.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.SieveFunctions118
open Set Filter intervalIntegral
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002
/-- The initial delay system has a concrete continuous solution on the intervals needed
for Lemma 2, pages 598 to 599. This proves the differential hypotheses are realizable.
It does not assert a linear sieve estimate or a global solution beyond these intervals. -/
theorem exists_local_sieve_functions118 : ∃ f F : ℝ → ℝ,
    (∀ s : ℝ, 0 < s → s ≤ 2 →
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s ∧ f s = 0) ∧
    ContinuousOn (fun s => s * F s) (Icc 2 5) ∧
    ContinuousOn (fun s => s * f s) (Icc 2 6) ∧
    (∀ s ∈ Ioo (2 : ℝ) 5, HasDerivAt (fun t => t * F t) (f (s - 1)) s) ∧
    (∀ s ∈ Ioo (2 : ℝ) 6, HasDerivAt (fun t => t * f t) (F (s - 1)) s) ∧
    Lemma2Formulas118 f F := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let g : ℝ → ℝ := fun t => Real.log (max t 2 - 1) / max t 2
  have hgcont : Continuous g := by
    apply Continuous.div
    · exact ((continuous_id.max continuous_const).sub continuous_const).log
        (fun t => by have := le_max_right t (2 : ℝ); dsimp; linarith)
    · exact continuous_id.max continuous_const
    · intro t
      have := le_max_right t (2 : ℝ)
      dsimp
      linarith
  have hgzero : ∀ t : ℝ, t ≤ 2 → g t = 0 := by
    intro t ht
    norm_num [g, max_eq_right ht]
  let G : ℝ → ℝ := fun t => ∫ u in (2 : ℝ)..t, g u
  have hGderiv : ∀ t : ℝ, HasDerivAt G (g t) t :=
    fun t => (hgcont.integral_hasStrictDerivAt 2 t).hasDerivAt
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr (fun t => (hGderiv t).continuousAt)
  have hGzero : ∀ t : ℝ, t ≤ 2 → G t = 0 := by
    intro t ht
    change (∫ u in (2 : ℝ)..t, g u) = 0
    calc
      _ = ∫ u in (2 : ℝ)..t, (0 : ℝ) := by
        apply integral_congr
        intro u hu
        apply hgzero
        rw [uIcc_of_ge ht] at hu
        exact hu.2
      _ = 0 := integral_zero
  let F : ℝ → ℝ := fun s => A / s * (1 + G (s - 1))
  have hFsmall : ∀ s : ℝ, 0 < s → s ≤ 3 → F s = A / s := by
    intro s hs hs3
    simp [F, hGzero (s - 1) (by linarith)]
  let k : ℝ → ℝ := fun t => (1 + G (max t 1 - 1)) / max t 1
  have hkcont : Continuous k := by
    apply Continuous.div
    · exact continuous_const.add (hGcont.comp ((continuous_id.max continuous_const).sub continuous_const))
    · exact continuous_id.max continuous_const
    · intro t
      have := le_max_right t (1 : ℝ)
      dsimp
      linarith
  let J : ℝ → ℝ := fun t => ∫ u in (1 : ℝ)..t, k u
  have hJderiv : ∀ t : ℝ, HasDerivAt J (k t) t :=
    fun t => (hkcont.integral_hasStrictDerivAt 1 t).hasDerivAt
  have hJcont : Continuous J := continuous_iff_continuousAt.mpr (fun t => (hJderiv t).continuousAt)
  let f : ℝ → ℝ := fun s => A / max s 2 * J (max (s - 1) 1)
  have hfzero : ∀ s : ℝ, s ≤ 2 → f s = 0 := by
    intro s hs
    have hm : max (s - 1) 1 = 1 := max_eq_right (by linarith)
    simp [f, hm, J]
  have hfcont : Continuous f := by
    apply Continuous.mul
    · exact continuous_const.div (continuous_id.max continuous_const)
        (fun s => by have := le_max_right s (2 : ℝ); dsimp; linarith)
    · exact hJcont.comp ((continuous_id.sub continuous_const).max continuous_const)
  have hSFcont : ContinuousOn (fun s => s * F s) (Icc (2 : ℝ) 5) := by
    apply continuousOn_id.mul
    apply ContinuousOn.mul
    · exact continuousOn_const.div continuousOn_id (fun s hs => by dsimp; linarith [hs.1])
    · exact continuousOn_const.add (hGcont.continuousOn.comp
        (continuousOn_id.sub continuousOn_const) (fun _ _ => mem_univ _))
  have hsfcont : ContinuousOn (fun s => s * f s) (Icc (2 : ℝ) 6) :=
    (continuous_id.mul hfcont).continuousOn
  have hfderiv : ∀ s : ℝ, 2 < s → HasDerivAt (fun t => t * f t) (F (s - 1)) s := by
    intro s hs
    have hd := (((hJderiv (s - 1)).comp s ((hasDerivAt_id s).sub_const 1)).const_mul A)
    have heq : (fun t => A * J (t - 1)) =ᶠ[𝓝 s] (fun t => t * f t) := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      dsimp [f]
      rw [max_eq_left ht.le, max_eq_left (by linarith : 1 ≤ t - 1)]
      field_simp
    have hv : A * (k (s - 1) * 1) = F (s - 1) := by
      dsimp [k, F]
      rw [max_eq_left (by linarith : 1 ≤ s - 1)]
      ring
    rw [hv] at hd
    exact hd.congr_of_eventuallyEq heq.symm
  have hfsmall : ∀ s ∈ Icc (2 : ℝ) 4, f s = A * Real.log (s - 1) / s := by
    intro s hs
    apply sieve_f_small118 f F hFsmall (hfzero 2 le_rfl)
    · exact hsfcont.mono (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
    · intro x hx
      exact hfderiv x hx.1
    · exact hs.1
    · exact hs.2
  have hFderiv : ∀ s ∈ Ioo (2 : ℝ) 5, HasDerivAt (fun t => t * F t) (f (s - 1)) s := by
    intro s hs
    have hd := (((hasDerivAt_const (s - 1) (1 : ℝ)).add (hGderiv (s - 1))).comp s
      ((hasDerivAt_id s).sub_const 1)).const_mul A
    have heq : (fun t => A * (1 + G (t - 1))) =ᶠ[𝓝 s] (fun t => t * F t) := by
      filter_upwards [eventually_gt_nhds (by linarith [hs.1] : (0 : ℝ) < s)] with t ht
      dsimp [F]
      field_simp
    have hv : A * ((0 + g (s - 1)) * 1) = f (s - 1) := by
      by_cases hs3 : s ≤ 3
      · rw [hgzero (s - 1) (by linarith), hfzero (s - 1) (by linarith)]
        ring
      · have hs3' : 3 < s := lt_of_not_ge hs3
        rw [hfsmall (s - 1) ⟨by linarith, by linarith [hs.2]⟩]
        dsimp [g]
        rw [max_eq_left (by linarith : 2 ≤ s - 1)]
        ring
    rw [hv] at hd
    exact hd.congr_of_eventuallyEq heq.symm
  have hinit : ∀ s : ℝ, 0 < s → s ≤ 2 →
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s ∧ f s = 0 := by
    intro s hs hs2
    exact ⟨hFsmall s hs (by linarith), hfzero s hs2⟩
  refine ⟨f, F, hinit, hSFcont, hsfcont, hFderiv, ?_, ?_⟩
  · exact fun s hs => hfderiv s hs.1
  · exact lemma2_from_delay118 f F hinit hSFcont hsfcont hFderiv (fun s hs => hfderiv s hs.1)
end LeanLab.Cai2002
