/-
P0044, Lemma 2, pages 598 to 599.
Elementary consequences of the differential equations of Lemma 1.
The existence and sieve interpretation of those functions stay cited.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
open Set intervalIntegral
noncomputable section
namespace LeanLab.Cai2002
/-- Lemma 2, page 598: the upper sieve function is 2 exp gamma over s up to three.
CONDITIONAL on the initial data and upper differential equation of Lemma 1.
Continuity is required only on the integration interval. -/
theorem sieve_F_small118 (f F : ℝ → ℝ)
    (hinit : ∀ s : ℝ, 0 < s → s ≤ 2 →
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s ∧ f s = 0)
    (hcont : ContinuousOn (fun s => s * F s) (Icc 2 3))
    (hderiv : ∀ s ∈ Ioo (2 : ℝ) 3, HasDerivAt (fun t => t * F t) (f (s - 1)) s)
    (s : ℝ) (hs : 0 < s) (hs3 : s ≤ 3) :
    F s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
  by_cases hs2 : s ≤ 2
  · exact (hinit s hs hs2).1
  have h2s : 2 ≤ s := le_of_lt (lt_of_not_ge hs2)
  have hzero : ∫ x in (2 : ℝ)..s, (0 : ℝ) = s * F s - 2 * F 2 := by
    apply integral_eq_sub_of_hasDerivAt_of_le h2s
    · exact hcont.mono (Icc_subset_Icc le_rfl hs3)
    · intro x hx
      have hx3 : x ∈ Ioo (2 : ℝ) 3 := ⟨hx.1, hx.2.trans_le hs3⟩
      have hz := (hinit (x - 1) (by linarith [hx.1]) (by linarith [hx3.2])).2
      simpa only [hz] using hderiv x hx3
    · exact intervalIntegrable_const
  have hF2 := (hinit 2 (by norm_num) le_rfl).1
  simp only [integral_zero, hF2] at hzero
  apply (eq_div_iff hs.ne').mpr
  linarith
/-- Lemma 2, page 599: the lower function on the interval from two to four.
CONDITIONAL on the first upper formula and the lower differential equation. -/
theorem sieve_f_small118 (f F : ℝ → ℝ)
    (hF : ∀ s : ℝ, 0 < s → s ≤ 3 → F s = 2 * Real.exp Real.eulerMascheroniConstant / s)
    (hf2 : f 2 = 0)
    (hcont : ContinuousOn (fun s => s * f s) (Icc 2 4))
    (hderiv : ∀ s ∈ Ioo (2 : ℝ) 4, HasDerivAt (fun t => t * f t) (F (s - 1)) s)
    (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  have hlogcont : ContinuousOn (fun x : ℝ => A * Real.log (x - 1)) (Icc 2 s) := by
    apply continuousOn_const.mul
    exact (continuousOn_id.sub continuousOn_const).log (fun x hx => by dsimp; linarith [hx.1])
  have hzero : ∫ x in (2 : ℝ)..s, (0 : ℝ) =
      (s * f s - A * Real.log (s - 1)) - (2 * f 2 - A * Real.log (2 - 1)) := by
    apply integral_eq_sub_of_hasDerivAt_of_le hs2
    · exact (hcont.mono (Icc_subset_Icc le_rfl hs4)).sub hlogcont
    · intro x hx
      have hx4 : x ∈ Ioo (2 : ℝ) 4 := ⟨hx.1, hx.2.trans_le hs4⟩
      have hh := (hderiv x hx4).sub
        ((((hasDerivAt_id x).sub_const 1).log (by dsimp; linarith [hx.1])).const_mul A)
      rw [hF (x - 1) (by linarith [hx.1]) (by linarith [hx4.2])] at hh
      convert hh using 1 <;> first | rfl | simp [A, div_eq_mul_inv]
    · exact intervalIntegrable_const
  norm_num [hf2] at hzero
  apply (eq_div_iff (by linarith : s ≠ 0)).mpr
  dsimp [A] at hzero
  linarith

/-- Lemma 2, page 599: the upper function on the interval from three to five.
CONDITIONAL on the first lower formula and the upper differential equation. -/
theorem sieve_F_large118 (f F : ℝ → ℝ)
    (hf : ∀ s ∈ Icc (2 : ℝ) 4,
      f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s)
    (hF3 : F 3 = 2 * Real.exp Real.eulerMascheroniConstant / 3)
    (hcont : ContinuousOn (fun s => s * F s) (Icc 3 5))
    (hderiv : ∀ s ∈ Ioo (3 : ℝ) 5, HasDerivAt (fun t => t * F t) (f (s - 1)) s)
    (s : ℝ) (hs3 : 3 ≤ s) (hs5 : s ≤ 5) :
    F s = 2 * Real.exp Real.eulerMascheroniConstant / s *
      (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let v : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hv : ContinuousOn v (Icc (2 : ℝ) 4) := by
    apply ContinuousOn.div
    · exact (continuousOn_id.sub continuousOn_const).log (fun x hx => by dsimp; linarith [hx.1])
    · exact continuousOn_id
    · intro x hx
      dsimp
      linarith [hx.1]
  have hint : IntervalIntegrable (fun x : ℝ => A * v (x - 1)) MeasureTheory.volume 3 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs3]
    apply continuousOn_const.mul
    apply hv.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    change 2 ≤ x - 1 ∧ x - 1 ≤ 4
    constructor <;> linarith [hx.1, hx.2]
  have hFTC : ∫ x in (3 : ℝ)..s, A * v (x - 1) = s * F s - 3 * F 3 := by
    apply integral_eq_sub_of_hasDerivAt_of_le hs3
    · exact hcont.mono (Icc_subset_Icc le_rfl hs5)
    · intro x hx
      have hx5 : x ∈ Ioo (3 : ℝ) 5 := ⟨hx.1, hx.2.trans_le hs5⟩
      have hval := hf (x - 1) ⟨by linarith [hx.1], by linarith [hx5.2]⟩
      convert hderiv x hx5 using 1
      dsimp [A, v]
      rw [hval]
      ring
    · exact hint
  rw [integral_const_mul, integral_comp_sub_right] at hFTC
  norm_num [hF3] at hFTC
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by linarith : s ≠ 0)).mpr
  dsimp [A, v] at hFTC
  nlinarith

/-- Lemma 2, page 599: the lower function on the interval from four to six.
CONDITIONAL on the second upper formula and the lower differential equation. -/
theorem sieve_f_large118 (f F : ℝ → ℝ)
    (hF : ∀ s ∈ Icc (3 : ℝ) 5,
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s *
        (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t))
    (hf4 : f 4 = 2 * Real.exp Real.eulerMascheroniConstant * Real.log 3 / 4)
    (hcont : ContinuousOn (fun s => s * f s) (Icc 4 6))
    (hderiv : ∀ s ∈ Ioo (4 : ℝ) 6, HasDerivAt (fun t => t * f t) (F (s - 1)) s)
    (s : ℝ) (hs4 : 4 ≤ s) (hs6 : s ≤ 6) :
    f s = 2 * Real.exp Real.eulerMascheroniConstant / s *
      (Real.log (s - 1) + ∫ t in (3 : ℝ)..(s - 1),
        (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u) := by
  let A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant
  let v : ℝ → ℝ := fun t => Real.log (t - 1) / t
  let w : ℝ → ℝ := fun t => (1 / t) * ∫ u in (2 : ℝ)..(t - 1), v u
  have hv : ContinuousOn v (Icc (2 : ℝ) 4) := by
    apply ContinuousOn.div
    · exact (continuousOn_id.sub continuousOn_const).log (fun x hx => by dsimp; linarith [hx.1])
    · exact continuousOn_id
    · intro x hx
      dsimp
      linarith [hx.1]
  have hvint : IntervalIntegrable v MeasureTheory.volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using hv
  have hprim : ContinuousOn (fun t => ∫ u in (2 : ℝ)..t, v u) (Icc (2 : ℝ) 4) := by
    simpa only [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using continuousOn_primitive_interval' hvint (show (2 : ℝ) ∈ uIcc 2 4 by norm_num)
  have hw : ContinuousOn w (Icc (3 : ℝ) 5) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.div continuousOn_id (fun x hx => by dsimp; linarith [hx.1])
    · apply hprim.comp (continuousOn_id.sub continuousOn_const)
      intro x hx
      change 2 ≤ x - 1 ∧ x - 1 ≤ 4
      constructor <;> linarith [hx.1, hx.2]
  have hint : IntervalIntegrable (fun x : ℝ => A * w (x - 1)) MeasureTheory.volume 4 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs4]
    apply continuousOn_const.mul
    apply hw.comp (continuousOn_id.sub continuousOn_const)
    intro x hx
    change 3 ≤ x - 1 ∧ x - 1 ≤ 5
    constructor <;> linarith [hx.1, hx.2]
  have hlogcont : ContinuousOn (fun x : ℝ => A * Real.log (x - 1)) (Icc 4 s) := by
    apply continuousOn_const.mul
    exact (continuousOn_id.sub continuousOn_const).log (fun x hx => by dsimp; linarith [hx.1])
  have hFTC : ∫ x in (4 : ℝ)..s, A * w (x - 1) =
      (s * f s - A * Real.log (s - 1)) - (4 * f 4 - A * Real.log (4 - 1)) := by
    apply integral_eq_sub_of_hasDerivAt_of_le hs4
    · exact (hcont.mono (Icc_subset_Icc le_rfl hs6)).sub hlogcont
    · intro x hx
      have hx6 : x ∈ Ioo (4 : ℝ) 6 := ⟨hx.1, hx.2.trans_le hs6⟩
      have hdlog : HasDerivAt (fun t => A * Real.log (t - 1)) (A / (x - 1)) x := by
        convert (((hasDerivAt_id x).sub_const 1).log (by dsimp; linarith [hx.1])).const_mul A using 1 <;>
          simp [div_eq_mul_inv]
      have hh := (hderiv x hx6).sub hdlog
      have hval : F (x - 1) - A / (x - 1) = A * w (x - 1) := by
        rw [hF (x - 1) ⟨by linarith [hx.1], by linarith [hx6.2]⟩]
        dsimp [A, w, v]
        ring
      rw [hval] at hh
      exact hh
    · exact hint
  rw [integral_const_mul, integral_comp_sub_right] at hFTC
  norm_num [hf4] at hFTC
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by linarith : s ≠ 0)).mpr
  dsimp [A, w, v] at hFTC
  nlinarith

/-- CITED. Lemma 2, pages 598 to 599, the four formulas for the sieve functions. -/
def Lemma2Formulas118 (f F : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → s ≤ 3 → F s = 2 * Real.exp Real.eulerMascheroniConstant / s) ∧
  (∀ s ∈ Icc (3 : ℝ) 5,
    F s = 2 * Real.exp Real.eulerMascheroniConstant / s *
      (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t)) ∧
  (∀ s ∈ Icc (2 : ℝ) 4,
    f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s) ∧
  (∀ s ∈ Icc (4 : ℝ) 6,
    f s = 2 * Real.exp Real.eulerMascheroniConstant / s *
      (Real.log (s - 1) + ∫ t in (3 : ℝ)..(s - 1),
        (1 / t) * ∫ u in (2 : ℝ)..(t - 1), Real.log (u - 1) / u))

/-- All four formulas of Lemma 2, pages 598 to 599.
CONDITIONAL on the continuous initial differential system from Lemma 1.
No existence or prime distribution statement is assumed silently. -/
theorem lemma2_from_delay118 (f F : ℝ → ℝ)
    (hinit : ∀ s : ℝ, 0 < s → s ≤ 2 →
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s ∧ f s = 0)
    (hFcont : ContinuousOn (fun s => s * F s) (Icc 2 5))
    (hfcont : ContinuousOn (fun s => s * f s) (Icc 2 6))
    (hFderiv : ∀ s ∈ Ioo (2 : ℝ) 5, HasDerivAt (fun t => t * F t) (f (s - 1)) s)
    (hfderiv : ∀ s ∈ Ioo (2 : ℝ) 6, HasDerivAt (fun t => t * f t) (F (s - 1)) s) :
    Lemma2Formulas118 f F := by
  have hFsmall : ∀ s : ℝ, 0 < s → s ≤ 3 →
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
    apply sieve_F_small118 f F hinit
    · exact hFcont.mono (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
    · intro x hx
      exact hFderiv x ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hfsmall : ∀ s ∈ Icc (2 : ℝ) 4,
      f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
    intro s hs
    apply sieve_f_small118 f F hFsmall (hinit 2 (by norm_num) le_rfl).2
    · exact hfcont.mono (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩)
    · intro x hx
      exact hfderiv x ⟨hx.1, hx.2.trans (by norm_num)⟩
    · exact hs.1
    · exact hs.2
  have hFlarge : ∀ s ∈ Icc (3 : ℝ) 5,
      F s = 2 * Real.exp Real.eulerMascheroniConstant / s *
        (1 + ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t) := by
    intro s hs
    apply sieve_F_large118 f F hfsmall (hFsmall 3 (by norm_num) le_rfl)
    · exact hFcont.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
    · intro x hx
      exact hFderiv x ⟨by linarith [hx.1], hx.2⟩
    · exact hs.1
    · exact hs.2
  refine ⟨hFsmall, hFlarge, hfsmall, ?_⟩
  intro s hs
  apply sieve_f_large118 f F hFlarge (by convert hfsmall 4 (by norm_num) using 1 <;> norm_num)
  · exact hfcont.mono (by intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  · intro x hx
    exact hfderiv x ⟨by linarith [hx.1], hx.2⟩
  · exact hs.1
  · exact hs.2

end LeanLab.Cai2002
