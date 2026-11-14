import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory Set intervalIntegral

noncomputable section

theorem setIntegral_Icc_pi_prod {n : ℕ} (f : Fin n → ℝ → ℝ) (lo hi : Fin n → ℝ)
    (hle : ∀ j, lo j ≤ hi j) :
    (∫ x in Icc lo hi, ∏ j, f j (x j)) = ∏ j, ∫ t in lo j..hi j, f j t := by
  have hmeas : MeasurableSet (Icc lo hi) := measurableSet_Icc
  rw [← MeasureTheory.integral_indicator hmeas]
  have hind : ∀ x : Fin n → ℝ,
      (Icc lo hi).indicator (fun x => ∏ j, f j (x j)) x =
        ∏ j, (Icc (lo j) (hi j)).indicator (fun t => f j t) (x j) := by
    intro x
    by_cases hx : x ∈ Icc lo hi
    · rw [Set.indicator_of_mem hx]
      simp only [Set.mem_Icc] at hx
      have hxj (j : Fin n) : x j ∈ Icc (lo j) (hi j) := ⟨hx.1 j, hx.2 j⟩
      simp only [Finset.prod_ite_eq', Set.indicator_of_mem, hxj]
    · classical
      have hex : ∃ j : Fin n, x j ∉ Icc (lo j) (hi j) := by
        by_contra hnone
        push_neg at hnone
        apply hx
        exact ⟨fun k => (hnone k).1, fun k => (hnone k).2⟩
      obtain ⟨j, hxj⟩ := hex
      have hz : (Icc (lo j) (hi j)).indicator (fun t => f j t) (x j) = 0 := by
        simp [hxj]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hz]
      simp [hx]
  simp_rw [hind]
  rw [MeasureTheory.integral_fin_nat_prod_volume_eq_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [MeasureTheory.integral_indicator (measurableSet_Icc)]
  rw [setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]
  rw [intervalIntegral.integral_of_le (hle j)]
