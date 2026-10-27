/-
AI wrote this Lean code for CODEX task51.
P0074 pages 10 and 11, equation 28 and the Type I step of Lemma 4.1.
No beta-sieve existence or fundamental lemma is asserted here.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Lemma31Proof

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- The finite divisor-weight expression in equation 28. -/
noncomputable def divisorWeight (D : ℕ) (weights : ℕ → ℝ) (n : ℤ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if (d : ℤ) ∣ n then weights d else 0

/-- Membership in the short interval is its pair of real endpoint inequalities. -/
theorem mem_shortInterval (t H : ℝ) (n : ℤ) :
    n ∈ shortInterval t H ↔ t - H ≤ (n : ℝ) ∧ (n : ℝ) ≤ t := by
  simp only [shortInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- Multiples of a positive integer in the interval correspond to a rescaled interval. -/
theorem interval_multiples_sum {d : ℕ} (hd : 0 < d) (t H α : ℝ) :
    (∑ n ∈ (shortInterval t H).filter (fun n => (d : ℤ) ∣ n),
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) =
      ∑ k ∈ shortInterval (t / d) (H / d),
        LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * ((d : ℝ) * α)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  refine Finset.sum_nbij' (fun n : ℤ => n / d) (fun k : ℤ => (d : ℤ) * k)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hl, hr⟩ := (mem_shortInterval t H n).mp hn
    rw [mem_shortInterval]
    have hncast : (n : ℝ) = (d : ℝ) * (n / d : ℤ) := by
      exact_mod_cast (Int.mul_ediv_cancel' hdn).symm
    constructor
    · rw [div_sub_div_same, div_le_iff₀ hdR]
      linarith
    · rw [le_div_iff₀ hdR]
      linarith
  · intro k hk
    obtain ⟨hl, hr⟩ := (mem_shortInterval _ _ k).mp hk
    rw [div_sub_div_same, div_le_iff₀ hdR] at hl
    rw [le_div_iff₀ hdR] at hr
    rw [Finset.mem_filter, mem_shortInterval]
    push_cast
    exact ⟨⟨by nlinarith only [hl], by nlinarith only [hr]⟩, dvd_mul_right _ _⟩
  · intro n hn
    exact Int.mul_ediv_cancel' (Finset.mem_filter.mp hn).2
  · intro k hk
    exact Int.mul_ediv_cancel_left k hdZ
  · intro n hn
    have he : (d : ℤ) * (n / d) = n := Int.mul_ediv_cancel' (Finset.mem_filter.mp hn).2
    have heR : (d : ℝ) * (n / d : ℤ) = (n : ℝ) := by exact_mod_cast he
    congr 1
    calc
      (n : ℝ) * α = ((d : ℝ) * (n / d : ℤ)) * α :=
        congrArg (fun x : ℝ => x * α) heR.symm
      _ = (n / d : ℤ) * ((d : ℝ) * α) := by ring

/-- Expanding equation 28 reduces the Fourier sum to sums over rescaled intervals. -/
theorem divisorWeight_expansion (D : ℕ) (weights : ℕ → ℝ) (t H α : ℝ) :
    (∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)) =
      ∑ d ∈ Finset.Icc 1 D, (weights d : ℂ) *
        ∑ k ∈ shortInterval (t / d) (H / d),
          LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * ((d : ℝ) * α)) := by
  unfold divisorWeight
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  rw [← interval_multiples_sum hdpos]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hdn : (d : ℤ) ∣ n <;> simp [hdn]

/-- The first Type I inequality only needs bounded divisor coefficients. -/
theorem divisorWeight_fourier_le (D : ℕ) (weights : ℕ → ℝ) (t H α : ℝ)
    (hweights : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      ∑ d ∈ Finset.Icc 1 D,
        ‖∑ k ∈ shortInterval (t / d) (H / d),
          LeanLab.PNTPort.LargeSieve.e ((k : ℝ) * ((d : ℝ) * α))‖ := by
  rw [divisorWeight_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_right (hweights d hd) (norm_nonneg _)

/-- A nonintegral frequency has both the counting and the geometric interval bound. -/
theorem shortInterval_exp_min_le {t H α : ℝ} (hH : 0 ≤ H) (hα : 0 < dist0 α) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      min (H + 1) (1 / (2 * dist0 α)) := by
  apply le_min
  · have hc := (abs_le.mp (shortInterval_card_error (t := t) hH)).2
    calc
      _ ≤ ∑ _n ∈ shortInterval t H, (1 : ℝ) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_e]
      _ = ((shortInterval t H).card : ℝ) := by simp
      _ ≤ H + 1 := by linarith
  · exact shortInterval_exp_sum_le t H α hα

#print axioms mem_shortInterval
#print axioms interval_multiples_sum
#print axioms divisorWeight_expansion
#print axioms divisorWeight_fourier_le
#print axioms shortInterval_exp_min_le
end LeanLab.Grimmelt2019.MainTerm
