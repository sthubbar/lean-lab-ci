/-
Narrow reuse of the smoothing proofs in LeanLab.Linnik.Decomp1532b.
Source Gallagher1970 page 330 Lemma 1 and page 331 Theorem 1.
The proof bodies are copied from the existing lab file into a separate namespace.
This avoids the broad Linnik module import without editing files outside BHP1997.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Linnik.U1394Fejer
import LeanLab.PNTPort.LargeSieve.Multiplicative

namespace LeanLab.BHP1997.Gallagher605
open Finset MeasureTheory Filter
open LeanLab.PNTPort.LargeSieve (norm_e e_add)
open scoped Topology
set_option maxHeartbeats 1600000

open FourierTransform
open LeanLab.Linnik.U1394Fejer
/-- Fourier inversion for the Fejer kernel used in Gallagher 1970 p.330. -/
theorem integral_fejer_exp (x : ℝ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej t : ℂ) = (tri x : ℂ) := by
  have hF : 𝓕 (fun u => (tri u : ℂ)) = fun t => (fej t : ℂ) := by
    funext t
    rw [fourier_tri, fej_eq_G]
  have hFi : Integrable (𝓕 (fun u => (tri u : ℂ))) := by
    rw [hF]
    exact integrable_fej.ofReal
  have hi := integrable_tri.fourierInv_fourier_eq hFi
    ((Complex.continuous_ofReal.comp continuous_tri).continuousAt (x := x))
  rw [Real.fourierInv_eq', hF] at hi
  convert hi using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Real.inner_apply, smul_eq_mul]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 2
  push_cast
  ring


/-- The scaled Fourier kernel for Gallagher 1970 p.330 Lemma 1. -/
theorem integral_fejer_exp_scaled (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t : ℝ, LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ) = (δ⁻¹ * tri (x / δ) : ℝ) := by
  have heq : (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) =
      fun t => (fun u => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) (δ * t) := by
    ext t
    congr 2
    field_simp
  rw [heq, Measure.integral_comp_mul_left (fun u : ℝ => LeanLab.PNTPort.LargeSieve.e ((x / δ) * u) * (fej u : ℂ)) δ, integral_fejer_exp]
  simp only [abs_of_pos (inv_pos.mpr hδ), Complex.real_smul, Complex.ofReal_mul]


/-- Integrability of the phase times Fejer weight. -/
theorem integrable_fejer_phase (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LeanLab.PNTPort.LargeSieve.e (x * t) * (fej (δ * t) : ℂ)) := by
  have hi := integrable_fej.comp_mul_left' hδ.ne'
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact Complex.continuous_ofReal.comp (continuous_fej.comp (continuous_const.mul continuous_id))
  · filter_upwards [] with t
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fej_nonneg _)]


/-- Exact smoothed Fourier energy for any finite real frequency family. -/
theorem fejer_exponential_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (freq : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ((∫ t : ℝ, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      (δ⁻¹ : ℂ) * ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (tri ((freq i - freq j) / δ) : ℂ) := by
  have heq (t : ℝ) : ((‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * (starRingEnd ℂ) (a j) * (LeanLab.PNTPort.LargeSieve.e ((freq i - freq j) * t) * (fej (δ * t) : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum,
      sum_mul_sum, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    rw [map_mul, ← LeanLab.PNTPort.LargeSieve.e_neg]
    rw [show (freq i - freq j) * t = freq i * t + -(freq j * t) by ring, e_add]
    ring
  rw [← integral_complex_ofReal]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (integrable_fejer_phase (freq i - freq j) hδ).const_mul _)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_fejer_phase (freq i - freq j) hδ).const_mul _),
    mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul, integral_fejer_exp_scaled _ hδ]
  push_cast
  ring


/-- The Fejer weight has an explicit positive lower bound near zero. -/
theorem fejer_lower_half {u : ℝ} (hu : |u| ≤ 1 / 2) : 4 / Real.pi ^ 2 ≤ fej u := by
  by_cases hz : u = 0
  · subst u
    have h0 : fej 0 = 1 := by simp [fej, LeanLab.PNTPort.LargeSieve.e]
    rw [h0, div_le_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
    nlinarith [Real.pi_gt_three]
  · have hs := LeanLab.PNTPort.LargeSieve.two_abs_le_abs_sin hu
    have hs2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * |u|) hs 2
    simp only [mul_pow, sq_abs] at hs2
    rw [fej_ne hz, le_div_iff₀ (by positivity : (0 : ℝ) < (Real.pi * u) ^ 2)]
    calc
      4 / Real.pi ^ 2 * (Real.pi * u) ^ 2 = 4 * u ^ 2 := by field_simp
      _ ≤ _ := by norm_num at hs2; exact hs2


/-- Integrability of a finite Fourier energy with Fejer weight. -/
theorem integrable_fejer_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
  have hsum (t : ℝ) : ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, norm_e, mul_one]
  have hi := (integrable_fej.comp_mul_left' hδ.ne').const_mul ((∑ i ∈ s, ‖a i‖) ^ 2)
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
    · exact continuous_fej.comp (continuous_const.mul continuous_id)
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (fej_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hsum t) 2) (fej_nonneg _)


/-- Finite frequency form of the smoothing step in Gallagher 1970 p.330 Lemma 1.
The triangle quadratic form is exactly the short interval energy kernel. -/
theorem gallagher_frequency_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ)) *
        (∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
          (tri ((freq i - freq j) / δ) : ℂ)).re := by
  have hc : Continuous (fun t : ℝ => ∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)) := by
    unfold LeanLab.PNTPort.LargeSieve.e; fun_prop
  have hw : Continuous (fun t : ℝ => ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
    (hc.norm.pow 2).mul (continuous_fej.comp (continuous_const.mul continuous_id))
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 ≤
        (Real.pi ^ 2 / 4) * (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) := by
    have ht' : |t| ≤ T := abs_le.mpr ht
    have hnear : |δ * t| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hδ]
      exact (mul_le_mul_of_nonneg_left ht' hδ.le).trans hδT
    have hlow := fejer_lower_half hnear
    have hone : (1 : ℝ) ≤ (Real.pi ^ 2 / 4) * fej (δ * t) := by
      calc
        1 = (Real.pi ^ 2 / 4) * (4 / Real.pi ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have hh := mul_le_mul_of_nonneg_left hone (sq_nonneg ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖)
    nlinarith
  have he := congrArg Complex.re (fejer_exponential_energy s a freq hδ)
  simp only [← Complex.ofReal_inv, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  calc
    _ ≤ ∫ t in (-T)..T, (Real.pi ^ 2 / 4) *
        (‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t)) :=
      intervalIntegral.integral_mono_on (by linarith) ((hc.norm.pow 2).intervalIntegrable _ _)
        ((continuous_const.mul hw).intervalIntegrable _ _) hpt
    _ = (Real.pi ^ 2 / 4) * ∫ t in (-T)..T,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi ^ 2 / 4) * ∫ t : ℝ,
        ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2 * fej (δ * t) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact setIntegral_le_integral (integrable_fejer_energy s a freq hδ)
        (Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (fej_nonneg _)))
    _ = _ := by rw [he]; ring


/-- The real interval overlap kernel behind Gallagher 1970 p.330 Lemma 1. -/
theorem interval_window_overlap (a b δ : ℝ) (_hδ : 0 ≤ δ) :
    ∫ x : ℝ, (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x = max 0 (δ - |a - b|) := by
  have heq : (fun x : ℝ => (Set.Icc (a - δ) a).indicator (fun _ => (1 : ℝ)) x *
      (Set.Icc (b - δ) b).indicator (fun _ => (1 : ℝ)) x) =
      (Set.Icc (a - δ) a ∩ Set.Icc (b - δ) b).indicator (fun _ => 1) := by
    ext x
    simp only [← Set.inter_indicator_mul, one_mul]
  rw [heq, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
    Set.Icc_inter_Icc, smul_eq_mul, mul_one, Real.volume_real_Icc]
  rw [max_comm]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right (by linarith : a - δ ≤ b - δ),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    congr 1; ring
  · rw [min_eq_right hba, max_eq_left (by linarith : b - δ ≤ a - δ),
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    congr 1; ring


/-- A finite short interval sum in the frequency variable. -/
noncomputable def frequencyWindow {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ x : ℝ) : ℂ :=
  ∑ i ∈ s, (Set.Icc (freq i - δ) (freq i)).indicator (fun _ => a i) x


/-- Exact overlap identity for the short interval energy in Gallagher p.330. -/
theorem frequency_window_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ((∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      (δ : ℂ) * ∑ i ∈ s, ∑ j ∈ s, a i * (starRingEnd ℂ) (a j) *
        (tri ((freq i - freq j) / δ) : ℂ) := by
  let A : ι → Set ℝ := fun i => Set.Icc (freq i - δ) (freq i)
  have hAi (i j : ι) : Integrable (fun x => (A i ∩ A j).indicator
      (fun _ => a i * (starRingEnd ℂ) (a j)) x) := by
    apply IntegrableOn.integrable_indicator _ (measurableSet_Icc.inter measurableSet_Icc)
    exact (continuous_const.integrableOn_Icc).mono_set Set.inter_subset_left
  have hpt (x : ℝ) : ((‖frequencyWindow s a freq δ x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator
        (fun _ => a i * (starRingEnd ℂ) (a j)) x := by
    unfold frequencyWindow
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    change (A i).indicator (fun _ => a i) x *
      (starRingEnd ℂ) ((A j).indicator (fun _ => a j) x) = _
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;>
      simp [hi, hj, Set.indicator_of_mem, Set.indicator_of_notMem]
  have hover (i j : ι) : volume.real (A i ∩ A j) =
      δ * tri ((freq i - freq j) / δ) := by
    have hi := interval_window_overlap (freq i) (freq j) δ hδ.le
    have he : (fun x : ℝ => (A i).indicator (fun _ => (1 : ℝ)) x *
        (A j).indicator (fun _ => (1 : ℝ)) x) =
        (A i ∩ A j).indicator (fun _ => (1 : ℝ)) := by
      ext x
      simp only [← Set.inter_indicator_mul, one_mul]
    change (∫ x : ℝ, (A i).indicator (fun _ => (1 : ℝ)) x *
      (A j).indicator (fun _ => (1 : ℝ)) x) = _ at hi
    rw [he, integral_indicator_const 1 (measurableSet_Icc.inter measurableSet_Icc),
      smul_eq_mul, mul_one] at hi
    rw [hi]
    unfold tri
    rw [abs_div, abs_of_pos hδ]
    by_cases h : |freq i - freq j| ≤ δ
    · rw [max_eq_right (by linarith), max_eq_right (by
        rw [sub_nonneg, div_le_one hδ]; exact h)]
      field_simp
    · have hh : δ < |freq i - freq j| := lt_of_not_ge h
      rw [max_eq_left (by linarith), max_eq_left (by
        rw [sub_nonpos, le_div_iff₀ hδ]; linarith)]
      ring
  rw [← integral_complex_ofReal]
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hAi i j)), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hAi i j), mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc), hover]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring


/-- Gallagher 1970 p.330 Lemma 1 for a finite family, with explicit constant.
Closed frequency windows change only finitely many endpoints in the outer integral. -/
theorem gallagher_window_smoothing {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 2) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, a i * LeanLab.PNTPort.LargeSieve.e (freq i * t)‖ ^ 2) ≤
      (Real.pi ^ 2 / (4 * δ ^ 2)) * ∫ x : ℝ, ‖frequencyWindow s a freq δ x‖ ^ 2 := by
  have he := congrArg Complex.re (frequency_window_energy s a freq hδ)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he
  have hh := gallagher_frequency_smoothing s a freq hδ hT hδT
  apply hh.trans_eq
  rw [he]
  field_simp



/-- Finite Dirichlet polynomial for Gallagher 1970 p.331 display 11. -/
noncomputable def characterPolynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * χ n * Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)



theorem integrable_frequencyWindow_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (δ : ℝ) :
    Integrable (fun x : ℝ => ‖frequencyWindow s a freq δ x‖ ^ 2) := by
  have hi : Integrable (frequencyWindow s a freq δ) := by
    unfold frequencyWindow
    apply integrable_finsetSum
    intro i _
    exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hb (x : ℝ) : ‖frequencyWindow s a freq δ x‖ ≤ ∑ i ∈ s, ‖a i‖ := by
    unfold frequencyWindow
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i _
    by_cases hx : x ∈ Set.Icc (freq i - δ) (freq i)
    · simp [hx]
    · simp [hx]
  apply (hi.norm.const_mul (∑ i ∈ s, ‖a i‖)).mono'
  · exact hi.aestronglyMeasurable.norm.pow 2
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (frequencyWindow s a freq δ x))
    nlinarith



/-- The scalar logarithmic window integral in the proof of Gallagher Theorem 3. -/
theorem integral_mellin_window_weight (l B δ : ℝ) (hδ : 0 ≤ δ) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u =
      δ * (B + 2) + (Real.exp δ - 1) * (Real.exp l - Real.exp (l - δ)) := by
  have he : (fun u : ℝ => (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u) =
      (Set.Icc (l - δ) l).indicator (fun u => Real.exp (u + δ) - Real.exp u + 2 + B) := by
    ext u
    by_cases hu : u ∈ Set.Icc (l - δ) l <;> simp [hu]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : l - δ ≤ l)]
  have hd (u : ℝ) : HasDerivAt
      (fun u => (Real.exp δ - 1) * Real.exp u + (B + 2) * u)
      (Real.exp (u + δ) - Real.exp u + 2 + B) u := by
    convert ((Real.hasDerivAt_exp u).const_mul (Real.exp δ - 1)).add
      ((hasDerivAt_id u).const_mul (B + 2)) using 1 <;> first | rfl | (rw [Real.exp_add]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (u + δ) - Real.exp u + 2 + B)).intervalIntegrable _ _)]
  ring


/-- The scalar window coefficient has the hybrid scale, not the pointwise T loss. -/
theorem mellin_window_weight_bound (l B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ u : ℝ, (Real.exp (u + δ) - Real.exp u + 2 + B) *
      (Set.Icc (l - δ) l).indicator (fun _ => (1 : ℝ)) u ≤
      δ * (B + 2) + 2 * δ ^ 2 * Real.exp l := by
  rw [integral_mellin_window_weight l B δ hδ]
  have habs : |δ| ≤ 1 := by rw [abs_of_nonneg hδ]; exact hδ1
  have h₁ : Real.exp δ - 1 ≤ 2 * δ := by
    have := Real.abs_exp_sub_one_le habs
    rw [abs_of_nonneg hδ] at this
    exact (le_abs_self _).trans this
  have h₂ : 1 - Real.exp (-δ) ≤ δ := by linarith [Real.add_one_le_exp (-δ)]
  have h₂0 : 0 ≤ 1 - Real.exp (-δ) := by
    have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ)
    linarith
  have hp := mul_le_mul h₁ h₂ h₂0 (by positivity : (0 : ℝ) ≤ 2 * δ)
  have he : Real.exp l - Real.exp (l - δ) = Real.exp l * (1 - Real.exp (-δ)) := by
    rw [Real.exp_sub, Real.exp_neg]
    ring
  rw [he]
  have hpe := mul_le_mul_of_nonneg_right hp (Real.exp_pos l).le
  nlinarith



/-- Rescaling the Dirichlet polynomial height by two pi. -/
theorem characterPolynomial_time_integral {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (∫ v in (-T)..T, ‖characterPolynomial χ a N v‖ ^ 2) =
      (2 * Real.pi) * ∫ t in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
        ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2 := by
  let c : ℝ := -1 / (2 * Real.pi)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let P : ℝ → ℝ := fun t => ‖∑ n ∈ Finset.Icc 1 N, (a n * χ n) * LeanLab.PNTPort.LargeSieve.e (Real.log n * t)‖ ^ 2
  have heq (v : ℝ) : ‖characterPolynomial χ a N v‖ ^ 2 = P (c * v) := by
    congr 2
    unfold characterPolynomial
    apply sum_congr rfl
    intro n _
    congr 1
    unfold LeanLab.PNTPort.LargeSieve.e
    congr 1
    dsimp [c]
    push_cast
    field_simp
  simp_rw [heq]
  rw [intervalIntegral.integral_comp_mul_left P hc]
  have h₁ : c * (-T) = T / (2 * Real.pi) := by dsimp [c]; ring
  have h₂ : c * T = -(T / (2 * Real.pi)) := by dsimp [c]; ring
  rw [h₁, h₂, intervalIntegral.integral_symm]
  dsimp [c, P]
  simp only [inv_div, inv_neg, inv_one, smul_eq_mul]
  ring



end LeanLab.BHP1997.Gallagher605
