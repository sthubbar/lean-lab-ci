import LeanLab.GoldbachAverage.Decomp287b

/-!
Goldston and Yang, arXiv 1601.06902v1 page 4 eq. 4.1 spatial integrability.
An L1 coefficient majorant has finite moving mass and a uniform bound.
Their product dominates the moving square.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.MovingIntegrability402
open MeasureTheory Set Filter
open Decomp287b

/-- The moving coefficient sum is measurable, GY page 4 before eq. 4.1.
Its summands are translated interval indicators. -/
theorem movingSum_measurable (a : ℕ → ℂ) (h : ℝ) :
    Measurable (fun x : ℝ => movingSum a x h) := by
  classical
  have he (x : ℝ) : movingSum a x h =
      ∑' n : ℕ, (Ico ((n : ℝ) - h) n).indicator (fun _ => a n) x := by
    apply tsum_congr
    intro n
    have hw : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔ x ∈ Ico ((n : ℝ) - h) n := by
      simp only [Set.mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases hx : x ∈ Ico ((n : ℝ) - h) n
    · rw [if_pos (hw.mpr hx), indicator_of_mem hx]
    · rw [if_neg (hw.not.mpr hx), indicator_of_notMem hx]
  simp_rw [he]
  exact Measurable.tsum (fun n => measurable_const.indicator measurableSet_Ico)

/-- A single unit coefficient has exactly h spatial square mass, GY page 4 eq. 4.1.
This nonzero instance checks the moving window normalization. -/
theorem unit_window_mass (h : ℝ) (hh : 0 ≤ h) :
    (∫ x : ℝ, ‖movingSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) x h‖ ^ 2) = h := by
  classical
  have hp (x : ℝ) : movingSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) x h =
      if x < 1 ∧ 1 ≤ x + h then 1 else 0 := by
    unfold movingSum
    rw [tsum_eq_single 1]
    · simp
    · intro n hn
      simp [hn]
  have he : (fun x : ℝ =>
      ‖movingSum (fun n : ℕ => if n = 1 then (1 : ℂ) else 0) x h‖ ^ 2) =
      (Ico (1 - h) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    rw [hp]
    have hw : x < 1 ∧ 1 ≤ x + h ↔ x ∈ Ico (1 - h) 1 := by
      simp only [Set.mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases hx : x ∈ Ico (1 - h) 1
    · simp [hw.mpr hx, hx]
    · simp [hw.not.mpr hx, hx]
  rw [he, integral_indicator measurableSet_Ico]
  simp [measureReal_def, Real.volume_Ico, hh]

/-- The spatial square integrability component of GY page 4 eq. 4.1.
The proof uses Tonelli for a nonnegative indicator majorant. -/
theorem moving_square_integrable_proved (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2) := by
  classical
  let u : ℕ → ℝ → ℝ := fun n => (Ico ((n : ℝ) - h) n).indicator (fun _ => ‖a n‖)
  let v : ℕ → ℝ → ℂ := fun n => (Ico ((n : ℝ) - h) n).indicator (fun _ => a n)
  let M : ℝ → ℝ := fun x => ∑' n, u n x
  let A : ℝ := ∑' n, ‖a n‖
  have hu0 (n : ℕ) (x : ℝ) : 0 ≤ u n x := by
    simp only [u, Set.indicator_apply]
    split_ifs <;> positivity
  have hub (n : ℕ) (x : ℝ) : u n x ≤ ‖a n‖ := by
    simp only [u, Set.indicator_apply]
    split_ifs <;> simp
  have hus (x : ℝ) : Summable (fun n => u n x) :=
    Summable.of_nonneg_of_le (fun n => hu0 n x) (fun n => hub n x) ha
  have hum (n : ℕ) : Measurable (u n) := measurable_const.indicator measurableSet_Ico
  have hM : Measurable M := Measurable.tsum hum
  have hM0 (x : ℝ) : 0 ≤ M x := tsum_nonneg (fun n => hu0 n x)
  have hMA (x : ℝ) : M x ≤ A := (hus x).tsum_le_tsum (fun n => hub n x) ha
  have hiM : Integrable M := by
    refine ⟨hM.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hM0)]
    have hconv (x : ℝ) : ENNReal.ofReal (M x) = ∑' n, ENNReal.ofReal (u n x) :=
      ENNReal.ofReal_tsum_of_nonneg (fun n => hu0 n x) (hus x)
    simp_rw [hconv]
    rw [lintegral_tsum (fun n => ((hum n).ennreal_ofReal).aemeasurable)]
    have hterm (n : ℕ) : (∫⁻ x : ℝ, ENNReal.ofReal (u n x)) =
        ENNReal.ofReal ‖a n‖ * ENNReal.ofReal h := by
      have he : (fun x => ENNReal.ofReal (u n x)) =
          (Ico ((n : ℝ) - h) n).indicator (fun _ => ENNReal.ofReal ‖a n‖) := by
        funext x
        simp only [u, Set.indicator_apply]
        split_ifs <;> simp_all
      rw [he, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
      congr 2
      ring
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (a n)) ha]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hvnorm (n : ℕ) (x : ℝ) : ‖v n x‖ = u n x := by
    simp only [u, v, Set.indicator_apply]
    split_ifs <;> simp_all
  have hvm (n : ℕ) : Measurable (v n) := measurable_const.indicator measurableSet_Ico
  have hv : Measurable (fun x => ∑' n, v n x) := Measurable.tsum hvm
  have heq (x : ℝ) : movingSum a x h = ∑' n, v n x := by
    apply tsum_congr
    intro n
    have hw : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔
        x ∈ Ico ((n : ℝ) - h) n := by
      simp only [Set.mem_Ico]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    dsimp only [v]
    by_cases hx : x ∈ Ico ((n : ℝ) - h) n
    · rw [if_pos (hw.mpr hx), indicator_of_mem hx]
    · rw [if_neg (hw.not.mpr hx), indicator_of_notMem hx]
  have hms : Measurable (movingSum a · h) := by
    convert hv using 1
    funext x
    exact heq x
  have hn (x : ℝ) : ‖movingSum a x h‖ ≤ M x := by
    rw [heq]
    have hs : Summable (fun n => ‖v n x‖) := by simpa only [hvnorm] using hus x
    simpa only [hvnorm] using norm_tsum_le_tsum_norm hs
  have hbound (x : ℝ) : ‖movingSum a x h‖ ^ 2 ≤ A * M x := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hn x) 2
    have hm := mul_le_mul_of_nonneg_right (hMA x) (hM0 x)
    nlinarith only [hs, hm]
  refine (hiM.const_mul A).mono' (hms.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbound x

/-- The moving sum belongs to L2, supplying the Plancherel domain in GY page 4 eq. 4.1. -/
theorem movingSum_memLp (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (h : ℝ) (hh : 0 < h) : MemLp (fun x : ℝ => movingSum a x h) 2 := by
  exact (memLp_two_iff_integrable_sq_norm (movingSum_measurable a h).aestronglyMeasurable).mpr
    (moving_square_integrable_proved a ha h hh)

end LeanLab.GoldbachAverage.MovingIntegrability402
