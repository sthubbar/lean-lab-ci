/-
P0093 pages 161 and 165 to 167. Exceptional prime mass and power series growth.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357b
import LeanLab.Linnik1951.Decomp357i
import LeanLab.Linnik1951.Asymptotics357

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- P0093 pages 165 and 166. The rational major arcs form a measurable set. -/
theorem measurable_major357 (N : ℕ) : MeasurableSet (majorArcs280 N) := by
  unfold majorArcs280
  simp only [Set.setOf_and, Set.setOf_exists]
  apply measurableSet_Icc.inter
  apply MeasurableSet.iUnion
  intro r
  apply MeasurableSet.inter
  · exact MeasurableSet.const _
  · exact isClosed_le (by fun_prop) continuous_const |>.measurableSet

/-- P0093 page 167 before equation 10.1. The actual large T minor set is measurable. -/
theorem measurable_exceptional357 (N : ℕ) (hN : 1 ≤ N) (η : ℝ) :
    MeasurableSet (exceptionalArcs280 N η) := by
  unfold exceptionalArcs280
  simp only [Set.setOf_and]
  exact measurableSet_Icc.inter ((measurable_major357 N).compl.inter
    (isOpen_lt continuous_const (continuous_power_fourier111 N hN).norm).measurableSet)

/-- LEAF. P0093 page 166 proof of Lemma 7, equations 9.1 and 9.3 before
multiplication by the bound on T. Lemma 5 and the rational arc cover from
Lemma 6 give a power saving for prime square mass on the exceptional set.
The saving one hundredth is weaker than the displayed saving five hundredths. -/
theorem exceptional_prime_mass357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 < N →
        (∫ α in exceptionalArcs280 N η, ‖primeFourier111 N α‖ ^ 2) ≤
          C * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) := by
  sorry

/-- LEAF. P0093 page 161 equation 7.1 and the triangle inequality.
The damped powers of two series is uniformly bounded by a constant times
log N. This leaf has no GRH or exceptional set hypothesis. -/
theorem power_uniform_log357 :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, ‖powerFourier111 N α‖ ≤ A * Real.log N := by
  exact power_uniform_log_proved357

/-- P0093 page 166 proof of Lemma 7. A uniform power series bound factors
out of the absolute arc integral, leaving only the prime square mass. -/
theorem arc_abs_le_prime_mass357 (k N : ℕ) (hN : 1 ≤ N) (s : Set ℝ)
    (hs : s ⊆ Set.Icc 0 1) (hms : MeasurableSet s) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ α ∈ s, ‖powerFourier111 N α‖ ≤ B) :
    |arcContribution280 k N s| ≤
      Real.exp 1 * B ^ k * (∫ α in s, ‖primeFourier111 N α‖ ^ 2) := by
  have hS := continuous_prime_fourier111 N hN
  have hP := continuous_power_fourier111 N hN
  have hF : Continuous (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) := by
    fun_prop
  have hInt : IntegrableOn (fun α : ℝ => primeFourier111 N α ^ 2 *
      powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) s :=
    hF.integrableOn_Icc.mono_set hs
  have hSq : IntegrableOn (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) s :=
    (hS.norm.pow 2).integrableOn_Icc.mono_set hs
  unfold arcContribution280
  rw [abs_mul, abs_of_pos (Real.exp_pos 1)]
  calc
    _ ≤ Real.exp 1 * ‖∫ α in s, primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, ‖primeFourier111 N α ^ 2 *
        powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (∫ α in s, B ^ k * ‖primeFourier111 N α‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      apply setIntegral_mono_on hInt.norm (hSq.const_mul _) hms
      intro α hα
      simp only [norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, mul_one]
      calc
        _ ≤ ‖primeFourier111 N α‖ ^ 2 * B ^ k := by gcongr; exact hT α hα
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

/-- P0093 page 166 equation 9.2. Exact exceptional_error280 statement.
CONDITIONAL on the exceptional prime mass and uniform T growth leaves. -/
theorem exceptional_error_decomposed357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ k : ℕ, 3 ≤ k →
      ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 < N →
        |arcContribution280 k N (exceptionalArcs280 N η)| ≤ ε * scale111 k N := by
  obtain ⟨η, hη, hη1, C, hC, Nc, hc⟩ := exceptional_prime_mass357 hG
  obtain ⟨A, hA, Na, ha⟩ := power_uniform_log357
  refine ⟨η, hη, hη1, ?_⟩
  intro k hk ε hε
  obtain ⟨Ne, he⟩ := power_saving_negligible357 (Real.exp 1 * A ^ k * C)
    (1 / 100) (by positivity) (by norm_num) k ε hε
  refine ⟨max 2 (max Nc (max Na Ne)), ?_⟩
  intro N hev hN
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hcN : Nc < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have haN : Na < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have heN : Ne < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hscale : (N : ℝ) ≤ scale111 k N := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast h2.le)
    have hr : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hl)
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hr)
  have hbound := arc_abs_le_prime_mass357 k N (by omega) (exceptionalArcs280 N η)
    (fun α hα => hα.1) (measurable_exceptional357 N (by omega) η)
    (A * Real.log N) (mul_nonneg hA.le hlog) (fun α _ => ha N haN α)
  calc
    _ ≤ Real.exp 1 * (A * Real.log N) ^ k *
        (C * (N : ℝ) ^ (1 - (1 / 100 : ℝ))) :=
      hbound.trans (mul_le_mul_of_nonneg_left (hc N hcN) (by positivity))
    _ = (Real.exp 1 * A ^ k * C) * (N : ℝ) ^ (1 - (1 / 100 : ℝ)) * Real.log N ^ k := by
      rw [mul_pow]; ring
    _ ≤ ε * N := he N heN
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale hε.le

end LeanLab.Linnik1951
