/-
Jia 1996 page 262 proof of Lemma 21.
Source https://doi.org/10.4064/aa-77-3-207-287.
Convert the existing lab short interval prime number theorem to the dyadic source form.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prime514

namespace LeanLab.Languasco2004.Decomp588e
open Real Finset LeanLab.BHP1997.Decomp132
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 262 Lemma 21 support: the discrete logarithmic integral has the dyadic main term. -/
theorem dyadic_logarithmic_sum {t : ℝ} (ht : 2 ≤ t) :
    |(∑ m ∈ Ioc ⌊t⌋₊ ⌊2 * t⌋₊, (1 : ℝ) / log m) - t / log t| ≤
      (t / log t) * (log 2 / log t + 1 / t) := by
  let s := Ioc ⌊t⌋₊ ⌊2 * t⌋₊
  have ht0 : 0 < t := by linarith
  have hL : 0 < log t := Real.log_pos (by linarith)
  have hV : 0 < log (2 * t) := Real.log_pos (by linarith)
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hLV : log t ≤ log (2 * t) := Real.log_le_log ht0 (by linarith)
  have hk : t - 1 ≤ (s.card : ℝ) ∧ (s.card : ℝ) ≤ t + 1 := by
    have he : (s.card : ℝ) = (⌊2 * t⌋₊ : ℝ) - (⌊t⌋₊ : ℝ) := by
      dsimp [s]
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : t ≤ 2 * t))]
    rw [he]
    constructor <;> linarith [Nat.floor_le ht0.le, Nat.floor_le (by linarith : 0 ≤ 2 * t),
      Nat.lt_floor_add_one t, Nat.lt_floor_add_one (2 * t)]
  have hweights : ∀ m ∈ s, 1 / log (2 * t) ≤ (1 : ℝ) / log m ∧ (1 : ℝ) / log m ≤ 1 / log t := by
    intro m hm
    have hm' := mem_Ioc.mp hm
    have htm : t < (m : ℝ) := Nat.lt_of_floor_lt hm'.1
    have hm2 : (m : ℝ) ≤ 2 * t :=
      (Nat.cast_le.mpr hm'.2).trans (Nat.floor_le (by linarith))
    have hmL : 0 < log m := Real.log_pos (by linarith)
    exact ⟨one_div_le_one_div_of_le hmL (Real.log_le_log (by linarith) hm2),
      one_div_le_one_div_of_le hL (Real.log_le_log ht0 htm.le)⟩
  have hlow := sum_le_sum (fun m hm => (hweights m hm).1)
  have hupp := sum_le_sum (fun m hm => (hweights m hm).2)
  simp only [sum_const, nsmul_eq_mul, mul_one_div] at hlow hupp
  have hlow' : (t - 1) / log (2 * t) ≤ ∑ m ∈ s, (1 : ℝ) / log m :=
    (div_le_div_of_nonneg_right hk.1 hV.le).trans hlow
  have hupp' : (∑ m ∈ s, (1 : ℝ) / log m) ≤ (t + 1) / log t :=
    hupp.trans (div_le_div_of_nonneg_right hk.2 hL.le)
  have herror : (t / log t) * (log 2 / log t + 1 / t) =
      (t / log t) * (log 2 / log t) + 1 / log t := by field_simp <;> ring
  have hdiff : t / log t - (t - 1) / log (2 * t) =
      (t / log t) * (log 2 / log (2 * t)) + 1 / log (2 * t) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne']
    field_simp
    <;> ring
  have hdiffB : t / log t - (t - 1) / log (2 * t) ≤
      (t / log t) * (log 2 / log t + 1 / t) := by
    rw [hdiff, herror]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hlog2.le hL hLV) (by positivity))
      (one_div_le_one_div_of_le hL hLV)
  have herrorL : 1 / log t ≤ (t / log t) * (log 2 / log t + 1 / t) := by
    rw [herror]
    exact le_add_of_nonneg_left (by positivity)
  apply abs_le.mpr
  change _ ≤ (∑ m ∈ s, (1 : ℝ) / log m) - t / log t ∧
    (∑ m ∈ s, (1 : ℝ) / log m) - t / log t ≤ _
  constructor
  · linarith
  · have he : (t + 1) / log t = t / log t + 1 / log t := by ring
    rw [he] at hupp'
    linarith

/-- Jia page 262 Lemma 21 prime range: the dyadic short interval prime number theorem.
This uses the existing clean lab short interval theorem, with no new analytic input. -/
theorem dyadic_prime_number_theorem :
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
      |(((Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime).card : ℝ) - t / log t| ≤
        η * (t / log t) := by
  intro η hη
  obtain ⟨C0, hC0⟩ := LeanLab.BHP1997.Prime514.pnt_short_interval 2 (by norm_num)
  let C := max C0 1
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hInvL := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hInvT := (tendsto_inv_atTop_zero : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0))
  have hlim := (hInvL.const_mul (2 * C + log 2)).add hInvT
  simp only [mul_zero, zero_add] at hlim
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp (hlim.eventually_le_const hη)
  refine ⟨max 2 (max C T0), by have := le_max_left (2 : ℝ) (max C T0); linarith, ?_⟩
  intro t ht
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hL := Real.log_pos (by linarith : 1 < t)
  have hV := Real.log_pos (by linarith : 1 < 2 * t)
  have hLV : log t ≤ log (2 * t) := Real.log_le_log ht0 (by linarith)
  have hCt : C ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hTt : T0 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hP := hC0 (2 * t) (by have := le_max_left C0 1; dsimp [C] at hCt; linarith)
    t (2 * t) (by linarith) (by linarith) le_rfl
  have hprime : (∑ m ∈ Ioc ⌊t⌋₊ ⌊2 * t⌋₊, primeWeight m) =
      (((Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime).card : ℝ) := by
    simp [primeWeight, ← sum_filter]
  rw [sum_sub_distrib, hprime] at hP
  have hPB : |(((Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime).card : ℝ) -
      (∑ m ∈ Ioc ⌊t⌋₊ ⌊2 * t⌋₊, (1 : ℝ) / log m)| ≤ (2 * C) * t / (log t)^2 := by
    calc _ ≤ C0 * (2 * t) * log (2 * t) ^ (-(2 : ℝ)) := hP
      _ ≤ C * (2 * t) * log (2 * t) ^ (-(2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = (2 * C) * t / (log (2 * t))^2 := by
        rw [Real.rpow_neg hV.le, Real.rpow_two]
        ring
      _ ≤ (2 * C) * t / (log t)^2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (sq_le_sq₀ hL.le hV.le |>.mpr hLV)
  have hQ := dyadic_logarithmic_sum ht2
  have htot := (abs_sub_le
    (((Ioc ⌊t⌋₊ ⌊2 * t⌋₊).filter Nat.Prime).card : ℝ)
    (∑ m ∈ Ioc ⌊t⌋₊ ⌊2 * t⌋₊, (1 : ℝ) / log m) (t / log t)).trans (add_le_add hPB hQ)
  have he : (2 * C) * t / (log t)^2 + (t / log t) * (log 2 / log t + 1 / t) =
      ((2 * C + log 2) * (log t)⁻¹ + t⁻¹) * (t / log t) := by field_simp <;> ring
  rw [he] at htot
  have hfinal := hT0 t hTt
  dsimp only [Function.comp_def] at hfinal
  exact htot.trans (mul_le_mul_of_nonneg_right hfinal (by positivity))

#print axioms dyadic_logarithmic_sum
#print axioms dyadic_prime_number_theorem
end
end LeanLab.Languasco2004.Decomp588e
