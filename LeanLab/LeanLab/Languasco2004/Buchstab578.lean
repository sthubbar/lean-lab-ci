/-
Jia 1996 page 261 displays 40 and 41.
Source https://doi.org/10.4064/aa-77-3-207-287.
Construct the continuous Buchstab solution by successive unit intervals.
This proves existence only. It asserts no global numerical estimate.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Languasco2004.Buchstab578
open Real intervalIntegral Filter
noncomputable section

/-- Display 40: finite method of steps approximants with a denominator clamped below one. -/
def step : ℕ → ℝ → ℝ
  | 0, u => 1 / max 1 u
  | k + 1, u => if u ≤ 2 then 1 / max 1 u else
      (1 + ∫ t in (1 : ℝ)..(u - 1), step k t) / max 1 u

/-- Display 40 support: each approximant agrees with the initial formula below two. -/
theorem step_initial (k : ℕ) (u : ℝ) (hu : u ≤ 2) :
    step k u = 1 / max 1 u := by
  cases k <;> simp only [step, ite_eq_left hu]

/-- Display 40 support: every finite approximant is globally continuous. -/
theorem step_continuous (k : ℕ) : Continuous (step k) := by
  have hd : Continuous (fun u : ℝ => max 1 u) := by fun_prop
  have hn (u : ℝ) : max 1 u ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  induction k with
  | zero => exact continuous_const.div hd hn
  | succ k ih =>
    have hi : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..(u - 1), step k t) :=
      continuous_parametric_intervalIntegral_of_continuous
        (show Continuous (Function.uncurry (fun (_ : ℝ) t => step k t)) from ih.comp continuous_snd)
        (by fun_prop)
    change Continuous (fun u : ℝ => if u ≤ 2 then 1 / max 1 u else
      (1 + ∫ t in (1 : ℝ)..(u - 1), step k t) / max 1 u)
    apply Continuous.if_le (continuous_const.div hd hn) ((continuous_const.add hi).div hd hn)
      continuous_id continuous_const
    intro u hu
    have hu2 : u = 2 := hu
    subst u
    norm_num

/-- Displays 40 and 41 support: the next step preserves each completed interval. -/
theorem step_stable (k : ℕ) (u : ℝ) (hu : u ≤ (k : ℝ) + 2) :
    step (k + 1) u = step k u := by
  induction k generalizing u with
  | zero =>
    have hu2 : u ≤ 2 := by simpa using hu
    rw [step_initial _ _ hu2, step_initial _ _ hu2]
  | succ k ih =>
    by_cases hu2 : u ≤ 2
    · rw [step_initial _ _ hu2, step_initial _ _ hu2]
    · simp only [step, ite_eq_right hu2]
      congr 2
      apply integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
      apply ih
      simp only [Nat.cast_add, Nat.cast_one] at hu
      linarith [ht.2]

/-- Display 41 support: stabilization persists through all later approximants. -/
theorem step_stable_of_le (k j : ℕ) (hkj : k ≤ j) (u : ℝ)
    (hu : u ≤ (k : ℝ) + 2) : step j u = step k u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  clear hkj
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show k + (d + 1) = (k + d) + 1 by omega]
    rw [step_stable (k + d) u (by push_cast; have hd := Nat.cast_nonneg (α := ℝ) d; linarith)]
    exact ih

/-- Display 41 support: any two completed approximants agree. -/
theorem step_independent (k j : ℕ) (u : ℝ)
    (hk : u ≤ (k : ℝ) + 2) (hj : u ≤ (j : ℝ) + 2) : step k u = step j u := by
  rcases le_total k j with h | h
  · exact (step_stable_of_le k j h u hk).symm
  · exact step_stable_of_le j k h u hj

/-- Display 40: choose a completed approximant for each argument. -/
def buchstab (u : ℝ) : ℝ := step ⌈max 0 u⌉₊ u

/-- Display 40 support: any completed approximant computes the defined function exactly. -/
theorem buchstab_eq_step (k : ℕ) (u : ℝ) (hu : u ≤ (k : ℝ) + 2) :
    buchstab u = step k u := by
  apply step_independent
  · have h := Nat.le_ceil (max 0 u)
    linarith [le_max_right (0 : ℝ) u]
  · exact hu

/-- Page 261: the constructed solution is continuous at every joining endpoint. -/
theorem buchstab_continuous : Continuous buchstab := by
  apply continuous_iff_continuousAt.mpr
  intro u
  obtain ⟨k, hk⟩ := exists_nat_gt u
  apply (step_continuous k).continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds (show u < (k : ℝ) + 2 by linarith)] with v hv
  exact buchstab_eq_step k v hv.le

/-- Display 40: the initial interval is the reciprocal function. -/
theorem buchstab_initial (u : ℝ) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : buchstab u = 1 / u := by
  rw [buchstab_eq_step 0 u (by simpa using hu2), step, max_eq_right hu1]

/-- Displays 40 and 41: the constructed solution satisfies the integrated delay equation. -/
theorem buchstab_recurrence (u : ℝ) (hu : 2 ≤ u) :
    u * buchstab u = 1 + ∫ t in (1 : ℝ)..(u - 1), buchstab t := by
  obtain ⟨k, hk⟩ := exists_nat_gt u
  have hi : (∫ t in (1 : ℝ)..(u - 1), buchstab t) =
      ∫ t in (1 : ℝ)..(u - 1), step k t := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
    exact buchstab_eq_step k t (by linarith [ht.2])
  rw [hi, buchstab_eq_step (k + 1) u (by push_cast; linarith)]
  by_cases hu2 : u ≤ 2
  · have heq : u = 2 := le_antisymm hu2 hu
    subst u
    norm_num [step_initial (k + 1) 2 (by norm_num)]
  · rw [step, ite_eq_right hu2, max_eq_right (show 1 ≤ u by linarith)]
    field_simp

/-- Display 40: an explicit continuous solution exists, with no numerical bound assumed. -/
theorem buchstab_exists :
    ∃ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) ∧
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) ∧
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) := by
  exact ⟨buchstab, buchstab_continuous.continuousOn, buchstab_initial, buchstab_recurrence⟩

/-- Page 261 display 40: the integrated initial problem has at most one solution above one.
This elementary uniqueness theorem does not use a numerical estimate. -/
theorem solution_unique (w v : ℝ → ℝ)
    (hw0 : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hv0 : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → v u = 1 / u)
    (hw : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t)
    (hv : ∀ u : ℝ, 2 ≤ u → u * v u = 1 + ∫ t in (1 : ℝ)..(u - 1), v t) :
    ∀ u : ℝ, 1 ≤ u → w u = v u := by
  have hstrip : ∀ k : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (k : ℝ) + 2 → w u = v u := by
    intro k
    induction k with
    | zero =>
      intro u hu1 hu2
      exact (hw0 u hu1 (by simpa using hu2)).trans (hv0 u hu1 (by simpa using hu2)).symm
    | succ k ih =>
      intro u hu1 huK
      by_cases hu2 : u ≤ 2
      · exact (hw0 u hu1 hu2).trans (hv0 u hu1 hu2).symm
      · have hi : (∫ t in (1 : ℝ)..(u - 1), w t) = ∫ t in (1 : ℝ)..(u - 1), v t := by
          apply integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
          apply ih t ht.1
          push_cast at huK
          linarith [ht.2]
        have hwu := hw u (by linarith)
        have hvu := hv u (by linarith)
        rw [hi] at hwu
        have hu0 : u ≠ 0 := by linarith
        exact mul_left_cancel₀ hu0 (hwu.trans hvu.symm)
  intro u hu
  obtain ⟨k, hk⟩ := exists_nat_gt u
  exact hstrip k u hu (by linarith)

/-- Page 261: any function with the source initial interval and recurrence equals the construction. -/
theorem solution_eq_buchstab (w : ℝ → ℝ)
    (hw0 : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hw : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) :
    ∀ u : ℝ, 1 ≤ u → w u = buchstab u := by
  exact solution_unique w buchstab hw0 buchstab_initial hw buchstab_recurrence

/-- Page 261 after display 40: the constructed solution has the logarithmic formula through three. -/
theorem buchstab_two_three (u : ℝ) (hu2 : 2 ≤ u) (hu3 : u ≤ 3) :
    buchstab u = (1 + log (u - 1)) / u := by
  have hi : (∫ t in (1 : ℝ)..(u - 1), buchstab t) = log (u - 1) := by
    calc
      _ = ∫ t in (1 : ℝ)..(u - 1), 1 / t := by
        apply integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
        exact buchstab_initial t ht.1 (by linarith [ht.2])
      _ = log (u - 1) := by
        rw [integral_one_div_of_pos zero_lt_one (by linarith : 0 < u - 1)]
        simp
  apply (eq_div_iff (by linarith : u ≠ 0)).mpr
  have h := buchstab_recurrence u hu2
  rw [hi] at h
  nlinarith

/-- Page 261 display 40: above two the weighted solution satisfies the differential equation. -/
theorem buchstab_weight_derivative (u : ℝ) (hu : 2 < u) :
    HasDerivAt (fun v : ℝ => v * buchstab v) (buchstab (u - 1)) u := by
  have hI := integral_hasDerivAt_right
    (buchstab_continuous.intervalIntegrable (1 : ℝ) (u - 1))
    buchstab_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    buchstab_continuous.continuousAt
  have hd := (hI.comp u ((hasDerivAt_id u).sub_const 1)).const_add 1
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact buchstab_recurrence v hv.le

/-- Page 261 display 42: the constructed solution has the source first derivative formula. -/
theorem buchstab_derivative (u : ℝ) (hu : 2 < u) :
    HasDerivAt buchstab ((buchstab (u - 1) - buchstab u) / u) u := by
  have hu0 : u ≠ 0 := by linarith
  have hd := (buchstab_weight_derivative u hu).div (hasDerivAt_id u) hu0
  have he : (fun v : ℝ => (v * buchstab v) / v) =ᶠ[nhds u] buchstab := by
    filter_upwards [eventually_ne_nhds hu0] with v hv
    simp [hv]
  have h := hd.congr_of_eventuallyEq he.symm
  simp only [id_eq] at h
  convert h using 1 <;> field_simp [hu0]

#print axioms step
#print axioms step_initial
#print axioms step_continuous
#print axioms step_stable
#print axioms step_stable_of_le
#print axioms step_independent
#print axioms buchstab
#print axioms buchstab_eq_step
#print axioms buchstab_continuous
#print axioms buchstab_initial
#print axioms buchstab_recurrence
#print axioms buchstab_exists
#print axioms solution_unique
#print axioms solution_eq_buchstab
#print axioms buchstab_two_three
#print axioms buchstab_weight_derivative
#print axioms buchstab_derivative
end
end LeanLab.Languasco2004.Buchstab578
