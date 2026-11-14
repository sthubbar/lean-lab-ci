/-
Jia 1996 page 261, the first numerical base bound in Lemma 20.
Source https://doi.org/10.4064/aa-77-3-207-287.
A logarithmic tangent replaces the finite grid for the interval two through three.
This does not prove the global bounds from three or four onward.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.BuchstabInitial316
import LeanLab.Languasco2004.Geometry565

namespace LeanLab.Languasco2004.Buchstab565
open Real intervalIntegral BuchstabInitial316 Geometry565
noncomputable section

/-- Page 261 Lemma 20: certify the tangent point used for the initial numerical upper bound. -/
theorem log_tangent_point_bound : Real.log (1250 / 709) ≤ (0.5672 : ℝ) := by
  have h := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 541 / 1959)
    (by norm_num : (541 / 1959 : ℝ) < 1) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Page 261 Lemma 20: the actual initial Buchstab formula is at most 0.5672 from two to three. -/
theorem buchstab_initial_upper (u : ℝ) (hu : 2 ≤ u) (hu3 : u ≤ 3) :
    buchstabInitial u ≤ 0.5672 := by
  rw [buchstabInitial_eq_log hu]
  have hy : 0 < u - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hy (by norm_num : (0 : ℝ) < 1250 / 709))
  rw [Real.log_div hy.ne' (by norm_num : (1250 / 709 : ℝ) ≠ 0)] at h
  have hc := log_tangent_point_bound
  apply (div_le_iff₀ (by linarith : 0 < u)).mpr
  norm_num at h
  linarith

/-- Pages 261 and 262 display 41: propagate any bounds on the initial strip to all later arguments.
CONDITIONAL ON the weighted recurrence and the initial strip bounds.
Continuity supplies the integral hypotheses at every induction step. -/
theorem global_strip_bounds (w : ℝ → ℝ) (l U : ℝ)
    (hc : ContinuousOn w (Set.Ici 2))
    (hbase : ∀ u ∈ Set.Icc (2 : ℝ) 3, l ≤ w u ∧ w u ≤ U)
    (hrec : ∀ j : ℕ, ∀ u ∈ Set.Icc (3 + (j : ℝ)) (4 + (j : ℝ)),
      u * w u = (3 + (j : ℝ)) * w (3 + (j : ℝ)) +
        ∫ t in (2 + (j : ℝ))..(u - 1), w t) :
    ∀ u : ℝ, 2 ≤ u → l ≤ w u ∧ w u ≤ U := by
  have hstrip : ∀ j : ℕ, ∀ u ∈ Set.Icc (2 + (j : ℝ)) (3 + (j : ℝ)),
      l ≤ w u ∧ w u ≤ U := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      intro u hu
      simp only [Nat.cast_add, Nat.cast_one] at hu
      have hK : 0 < 3 + (j : ℝ) := by positivity
      have hKu : 3 + (j : ℝ) ≤ u := by linarith [hu.1]
      have hwK := ih (3 + (j : ℝ)) ⟨by linarith, le_rfl⟩
      have hint : IntervalIntegrable w MeasureTheory.volume
          ((3 + (j : ℝ)) - 1) (u - 1) := by
        apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        apply hc.mono
        intro t ht
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        exact le_trans (by linarith) ht.1
      have hb : ∀ t ∈ Set.Icc ((3 + (j : ℝ)) - 1) (u - 1), l ≤ w t ∧ w t ≤ U := by
        intro t ht
        exact ih t ⟨by linarith [ht.1], by linarith [ht.2, hu.2]⟩
      have hr := hrec j u ⟨hKu, by linarith [hu.2]⟩
      have hr' : u * w u = (3 + (j : ℝ)) * w (3 + (j : ℝ)) +
          ∫ t in ((3 + (j : ℝ)) - 1)..(u - 1), w t := by
        convert hr using 1 <;> congr 1 <;> ring
      exact buchstab_strip_from_recurrence w (3 + (j : ℝ)) u l U hK hKu hwK hint hb hr'
  intro u hu
  let j := ⌊u - 2⌋₊
  have hjL : (j : ℝ) ≤ u - 2 := Nat.floor_le (by linarith)
  have hjU : u - 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one (u - 2)
  exact hstrip j u ⟨by linarith, by linarith⟩

/-- Display 41: the constant unit function satisfies every global propagation hypothesis. -/
theorem global_strip_instance : ∀ u : ℝ, 2 ≤ u → (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 := by
  apply global_strip_bounds (fun _ => (1 : ℝ)) 1 1 (by fun_prop)
  · intro u hu
    exact ⟨le_rfl, le_rfl⟩
  · intro j u hu
    simp only [mul_one, integral_const, smul_eq_mul]
    ring

#print axioms global_strip_bounds
#print axioms global_strip_instance
#print axioms log_tangent_point_bound
#print axioms buchstab_initial_upper
end
end LeanLab.Languasco2004.Buchstab565
