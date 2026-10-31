/-
P0087 Akeno 2026 page 4, the exact Poisson step in Lemma 2.2.
The uniform decay estimate remains a separate analytic leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026.Localization86
open Real Finset
open scoped ContDiff SchwartzMap FourierTransform
open LeanLab.Akeno2026
/-- The modulated and scaled weight in the proof of Lemma 2.2. -/
noncomputable def modulatedWeight (w : ℝ → ℝ) (X α : ℝ) (x : ℝ) : ℂ :=
  e (α * x) * (w (x / X) : ℂ)
/-- LEAF. Page 4, modulation and scaling preserve smoothness. -/
theorem modulatedWeight_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (X α : ℝ) :
    ContDiff ℝ ∞ (modulatedWeight w X α) := by
  unfold modulatedWeight e
  have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact ((contDiff_const.mul (hc.comp (contDiff_const.mul contDiff_id))).cexp).mul
    (hc.comp (hw.comp (contDiff_id.div_const X)))
/-- LEAF. Page 4, the scaled weight has support in the interval from zero to X. -/
theorem modulatedWeight_support {w : ℝ → ℝ} (hs : Function.support w ⊆ Set.Icc 0 1)
    {X : ℝ} (hX : 0 < X) (α : ℝ) :
    Function.support (modulatedWeight w X α) ⊆ Set.Icc 0 X := by
  intro x hx
  have hwx : w (x / X) ≠ 0 := by
    intro hz
    have : modulatedWeight w X α x = 0 := by simp [modulatedWeight, hz]
    exact hx this
  have hh := hs hwx
  constructor
  · simpa using (le_div_iff₀ hX).mp hh.1
  · simpa using (div_le_iff₀ hX).mp hh.2

/-- The smooth compactly supported modulated weight as a Mathlib Schwartz map. -/
noncomputable def modulatedSchwartz (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (X : ℝ) (hX : 0 < X) (α : ℝ) :
    𝓢(ℝ, ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (modulatedWeight_support hs hX α)).toSchwartzMap (modulatedWeight_contDiff hw X α)
/-- LEAF. Page 4, exact Poisson summation before Fourier scaling and decay estimates. -/
theorem poisson_modulated (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (X : ℝ) (hX : 0 < X) (α : ℝ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) ⌊X⌋, e (α * n) * (w ((n : ℝ) / X) : ℂ)) =
      ∑' n : ℤ, (𝓕 (modulatedSchwartz w hw hs X hX α)) (n : ℝ) := by
  have hp := SchwartzMap.tsum_eq_tsum_fourier (modulatedSchwartz w hw hs X hX α) 0
  have hfin : (∑' n : ℤ, modulatedWeight w X α (n : ℝ)) =
      ∑ n ∈ Finset.Icc (0 : ℤ) ⌊X⌋, modulatedWeight w X α (n : ℝ) := by
    apply tsum_eq_sum
    intro n hn
    apply Function.notMem_support.mp
    intro hm
    have hh := modulatedWeight_support hs hX α hm
    apply hn
    simp only [Finset.mem_Icc, Int.le_floor]
    exact ⟨by exact_mod_cast hh.1, hh.2⟩
  have hp' : (∑' n : ℤ, modulatedWeight w X α (n : ℝ)) =
      ∑' n : ℤ, (𝓕 (modulatedSchwartz w hw hs X hX α)) (n : ℝ) := by
    simpa [modulatedSchwartz] using hp
  simpa only [modulatedWeight] using hfin.symm.trans hp'

/-- LEAF. Page 4, Fourier scaling and modulation by an exact change of variables. -/
theorem fourier_modulated (w : ℝ → ℝ) {X : ℝ} (hX : 0 < X) (α t : ℝ) :
    (𝓕 (modulatedWeight w X α)) t =
      (X : ℂ) * ∫ y : ℝ, e (-(X * (t - α)) * y) * (w y : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have heq : (fun v : ℝ => Complex.exp (↑(-2 * π * v * t) * Complex.I) • modulatedWeight w X α v) =
      (fun v : ℝ => e (-(X * (t - α)) * (v / X)) * (w (v / X) : ℂ)) := by
    funext v
    simp only [modulatedWeight, e, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']
    ring
  rw [heq]
  have hi := MeasureTheory.Measure.integral_comp_div
    (fun y : ℝ => e (-(X * (t - α)) * y) * (w y : ℂ)) X
  simpa only [abs_of_pos hX, Complex.real_smul] using hi

/-- The Fourier integral convention used in the proof of Lemma 2.2. -/
noncomputable def weightFourier (w : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, e (-t * y) * (w y : ℂ)

/-- LEAF. Page 4, the exact Poisson formula with the printed Fourier scaling. -/
theorem poisson_scaled (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (X : ℝ) (hX : 0 < X) (α : ℝ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) ⌊X⌋, e (α * n) * (w ((n : ℝ) / X) : ℂ)) =
      ∑' n : ℤ, (X : ℂ) * weightFourier w (X * ((n : ℝ) - α)) := by
  rw [poisson_modulated w hw hs X hX α]
  apply tsum_congr
  intro n
  exact fourier_modulated w hX α n

/-- LEAF. Page 4, the Fourier transform of a smooth compactly supported weight decays
faster than every fixed polynomial, with one constant for all frequencies. -/
theorem weightFourier_decay (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (1 + |t|) ^ j * ‖weightFourier w t‖ ≤ C := by
  let f := 𝓕 (modulatedSchwartz w hw hs 1 (by norm_num) 0)
  let C : ℝ := 2 ^ j * (Finset.Iic (j, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  refine ⟨max C 1, by positivity, ?_⟩
  intro t
  have ht := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (j, 0)) (k := j) (n := 0) le_rfl le_rfl f t
  have heq : f t = weightFourier w t := by
    change (𝓕 (modulatedWeight w 1 0)) t = weightFourier w t
    simpa [weightFourier] using (fourier_modulated w (X := 1) (by norm_num) 0 t)
  have hh : (1 + |t|) ^ j * ‖weightFourier w t‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, heq] using ht
  exact hh.trans (le_max_left _ _)

end LeanLab.Akeno2026.Localization86
