/-
AI wrote this Lean code for CODEX task58.
Elementary bounds for the integrals in U1435.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58Integrands

open Real intervalIntegral MeasureTheory Set Finset

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- The inner primitive on its full integration interval. -/
def H (v : ℝ) : ℝ := ∫ u in (2 : ℝ)..v, inner u

theorem inner_le_quarter {u : ℝ} (hu : u ∈ Set.Icc 2 3) : inner u ≤ 1 / 4 := by
  have h := inner_monotone hu (show (3 : ℝ) ∈ Set.Icc 2 3 by norm_num) hu.2
  have hl := log_two_lt_d9
  norm_num [inner] at h
  unfold inner
  linarith

theorem inner_integrable {a b : ℝ} (ha : a ∈ Set.Icc 2 3) (hb : b ∈ Set.Icc 2 3) :
    IntervalIntegrable inner volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply inner_continuous.mono
  exact uIcc_subset_Icc ha hb

theorem H_bounds {v : ℝ} (hv : v ∈ Set.Icc 2 3) : 0 ≤ H v ∧ H v ≤ (v - 2) / 4 := by
  constructor
  · exact integral_nonneg hv.1 (fun x hx => inner_nonneg ⟨hx.1, hx.2.trans hv.2⟩)
  · have h := integral_mono_on hv.1
      (inner_integrable (by norm_num) hv) (intervalIntegrable_const (c := (1 / 4 : ℝ)))
      (fun x hx => inner_le_quarter ⟨hx.1, hx.2.trans hv.2⟩)
    simpa [H, div_eq_mul_inv] using h

theorem H_continuous : ContinuousOn H (Set.Icc 2 3) := by
  have h := continuousOn_primitive_interval' (inner_integrable (a := 2) (b := 3) (by norm_num) (by norm_num))
    (show (2 : ℝ) ∈ Set.uIcc 2 3 by norm_num)
  change ContinuousOn (fun v : ℝ => ∫ u in (2 : ℝ)..v, inner u) (Set.Icc 2 3)
  simpa only [uIcc_of_le (show (2 : ℝ) ≤ 3 by norm_num)] using h

theorem H_monotone : MonotoneOn H (Set.Icc 2 3) := by
  intro x hx y hy hxy
  have h : (0 : ℝ) ≤ ∫ t in x..y, inner t :=
    intervalIntegral.integral_nonneg hxy (fun t ht => inner_nonneg ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)
  have he := integral_add_adjacent_intervals (inner_integrable (a := 2) (by norm_num) hx)
    (inner_integrable hx hy)
  dsimp [H]
  linarith

theorem Fn_on {s : ℝ} (hs : s ∈ Set.Icc 3 4) : U1435.Fn s = 1 + H (s - 1) := by
  unfold U1435.Fn
  split_ifs with h
  · have he : s = 3 := by linarith [hs.1]
    subst s
    norm_num [H]
  · rfl

theorem Fn_bounds {s : ℝ} (hs : s ∈ Set.Icc 3 4) :
    1 ≤ U1435.Fn s ∧ U1435.Fn s ≤ 1 + (s - 3) / 4 := by
  have h := H_bounds (v := s - 1) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [Fn_on hs]
  constructor <;> linarith

theorem Fn_continuous : ContinuousOn U1435.Fn (Set.Icc 3 4) := by
  have h : ContinuousOn (fun s : ℝ => 1 + H (s - 1)) (Set.Icc 3 4) :=
    continuousOn_const.add (H_continuous.comp (continuousOn_id.sub continuousOn_const)
      (by intro x hx; constructor <;> linarith [hx.1, hx.2]))
  exact h.congr (fun x hx => Fn_on hx)

theorem Fn_monotone : MonotoneOn U1435.Fn (Set.Icc 3 4) := by
  intro x hx y hy hxy
  rw [Fn_on hx, Fn_on hy]
  have h : H (x - 1) ≤ H (y - 1) := H_monotone
    (show x - 1 ∈ Set.Icc (2 : ℝ) 3 from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    (show y - 1 ∈ Set.Icc (2 : ℝ) 3 from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    (by linarith)
  linarith

theorem J1_nonneg : 0 ≤ U1435.J1 := by
  unfold U1435.J1
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact div_nonneg (H_bounds (v := t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩).1
    (by linarith [ht.1])


/-- The outer integrand defining J1. -/
def j1Kernel (t : ℝ) : ℝ := H (t - 1) / t

/-- The outer integrand defining J2. -/
def j2Kernel (t : ℝ) : ℝ := U1435.Fn (5 - 10 * t) / (t * (5 - 10 * t))

theorem j1Kernel_continuous : ContinuousOn j1Kernel (Set.Icc 3 4) := by
  apply ContinuousOn.div
  · exact H_continuous.comp (continuousOn_id.sub continuousOn_const)
      (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  · exact continuousOn_id
  · intro x hx; linarith [hx.1]

theorem j2Kernel_continuous : ContinuousOn j2Kernel (Set.Icc (1 / 10 : ℝ) (1 / 5)) := by
  apply ContinuousOn.div
  · exact Fn_continuous.comp (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  · exact continuousOn_id.mul (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
  · intro x hx
    exact mul_ne_zero (by linarith [hx.1]) (by linarith [hx.2])

theorem j2Kernel_antitone : AntitoneOn j2Kernel (Set.Icc (1 / 10 : ℝ) (1 / 5)) := by
  intro x hx y hy hxy
  have hsx : 5 - 10 * x ∈ Set.Icc (3 : ℝ) 4 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsy : 5 - 10 * y ∈ Set.Icc (3 : ℝ) 4 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hnum := Fn_monotone hsy hsx (by linarith)
  have hden : x * (5 - 10 * x) ≤ y * (5 - 10 * y) := by nlinarith [hx.1, hy.2]
  exact div_le_div₀ (by linarith [(Fn_bounds hsx).1]) hnum
    (mul_pos (by linarith [hx.1]) (by linarith [hx.2])) hden

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_le_quarter
#print axioms LeanLab.ChenPrimeExceptional.Task58.inner_integrable
#print axioms LeanLab.ChenPrimeExceptional.Task58.H_bounds
#print axioms LeanLab.ChenPrimeExceptional.Task58.H_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.H_monotone
#print axioms LeanLab.ChenPrimeExceptional.Task58.Fn_on
#print axioms LeanLab.ChenPrimeExceptional.Task58.Fn_bounds
#print axioms LeanLab.ChenPrimeExceptional.Task58.Fn_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.Fn_monotone
#print axioms LeanLab.ChenPrimeExceptional.Task58.J1_nonneg

#print axioms LeanLab.ChenPrimeExceptional.Task58.j1Kernel_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Kernel_continuous
#print axioms LeanLab.ChenPrimeExceptional.Task58.j2Kernel_antitone
