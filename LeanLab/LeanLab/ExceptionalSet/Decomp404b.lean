import LeanLab.ExceptionalSet.PrimeKernel264

/-!
P0082 page 356, the periodization step in the proof of Lemma 1.
Source: https://doi.org/10.5802/aif.1621
This version assumes integrability of the product explicitly.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp404b

open Real MeasureTheory Filter Asymptotics
open scoped FourierTransform
open LeanLab.ExceptionalSet.U1539

/-- P0082 page 356, first proof display. An integrable function on the
real line equals the period integral of its sum of integer translates. -/
theorem integral_periodization (g : ℝ → ℂ) (hg : Integrable g) :
    (∫ x, g x) = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, g (x + n) := by
  have hi (n : ℤ) : Integrable (fun x : ℝ => g (x + n)) (volume.restrict (Set.Ioc 0 1)) := by
    exact (hg.comp_add_right (n : ℝ)).integrableOn
  have hs : Summable (fun n : ℤ => ∫ x in Set.Ioc (0 : ℝ) 1, ‖g (x + n)‖) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      hg.norm.hasSum_intervalIntegral_comp_add_int.summable
  calc
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, g (x + n) :=
      hg.hasSum_intervalIntegral_comp_add_int.tsum_eq.symm
    _ = _ := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact integral_tsum_of_summable_integral_norm hi hs

/-- P0082 page 356, first proof display. For periodic h and an integrable
modulated product, folding follows from Bochner summation and the period. -/
theorem fold_of_integrable (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
    (hg : Integrable (fun x : ℝ => h x * K x * eC (-(x * v)))) :
    (∫ x, h x * K x * eC (-(x * v))) =
      ∫ x in (0 : ℝ)..1, h x * (∑' n : ℤ, K (x + n) * eC (-((x + n) * v))) := by
  rw [integral_periodization _ hg]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have he (n : ℤ) : h (x + n) = h x := by
    simpa only [mul_one] using hper.int_mul n x
  simp_rw [he, mul_assoc]
  exact tsum_mul_left

/-- P0082 page 357 display 4. The explicit kernel has quadratic decay.
The constant two follows directly from the two squared sine numerators. -/
theorem kernel_decay (Δ x : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hx : x ≠ 0) :
    ‖(Kfun Δ x : ℂ)‖ ≤ (2 / (Δ * Real.pi ^ 2)) * |x| ^ (-2 : ℝ) := by
  have hp : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  have hq : Real.pi * (1 - Δ) * x ≠ 0 :=
    mul_ne_zero (mul_ne_zero Real.pi_ne_zero (by linarith)) hx
  have he : Kfun Δ x =
      (Real.sin (Real.pi * x) ^ 2 - Real.sin (Real.pi * (1 - Δ) * x) ^ 2) /
        (Δ * Real.pi ^ 2 * x ^ 2) := by
    rw [Kfun, Real.sinc_of_ne_zero hp, Real.sinc_of_ne_zero hq]
    field_simp
  have hden : 0 < Δ * Real.pi ^ 2 * x ^ 2 := by positivity
  have hs (y : ℝ) : Real.sin y ^ 2 ≤ 1 := by
    nlinarith [Real.abs_sin_le_one y, sq_nonneg (Real.cos y), Real.sin_sq_add_cos_sq y]
  have hnum : |Real.sin (Real.pi * x) ^ 2 - Real.sin (Real.pi * (1 - Δ) * x) ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hs (Real.pi * x), hs (Real.pi * (1 - Δ) * x),
      sq_nonneg (Real.sin (Real.pi * x)), sq_nonneg (Real.sin (Real.pi * (1 - Δ) * x))]
  simp only [Complex.norm_real, Real.norm_eq_abs, he, abs_div, abs_of_pos hden]
  calc
    _ ≤ 2 / (Δ * Real.pi ^ 2 * x ^ 2) := div_le_div_of_nonneg_right hnum hden.le
    _ = _ := by
      rw [Real.rpow_neg (abs_nonneg x), Real.rpow_two, sq_abs]
      ring

/-- P0082 page 356 Fourier convention. The paper transform is Mathlib's
Fourier integral on the real line. -/
theorem ftR_eq_fourier (K : ℝ → ℂ) (y : ℝ) :
    ftR K y = FourierTransform.fourier K y := by
  simp only [ftR, eC, Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hx : 2 * (Real.pi : ℂ) * Complex.I * (-(y * x) : ℝ) =
      ↑(-2 * Real.pi * x * y) * Complex.I := by push_cast; ring
  rw [hx]
  ring

/-- P0082 page 356 Poisson proof. Modulation translates the explicit
kernel transform to the trapezoid evaluated at v plus y. -/
theorem fourier_modulated_kernel (Δ v y : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    FourierTransform.fourier (fun x : ℝ => (Kfun Δ x : ℂ) * eC (-(x * v))) y =
      (KernelTransform264.weight Δ (v + y) : ℂ) := by
  rw [← ftR_eq_fourier, ← KernelTransform264.ftR_Kfun hΔ hΔ1 (v + y)]
  unfold ftR
  apply integral_congr_ae
  filter_upwards with x
  unfold eC
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- P0082 page 357 display 4. The modulated paper kernel satisfies
Mathlib's quadratic decay hypothesis for Poisson summation. -/
theorem modulated_kernel_isBigO (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (fun x : ℝ => (Kfun Δ x : ℂ) * eC (-(x * v))) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  apply IsBigO.of_bound (2 / (Δ * Real.pi ^ 2))
  filter_upwards [(isCompact_singleton : IsCompact ({0} : Set ℝ)).compl_mem_cocompact] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simpa only [norm_mul, norm_eC, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)] using kernel_decay Δ x hΔ hΔ1 hx0

/-- P0082 page 356 Poisson display. At integer frequencies the translated
trapezoid is supported on the two integers adjacent to minus v. -/
theorem weight_integer_support (Δ v : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (m : ℤ)
    (hm : m ∉ ({-⌊v⌋, -⌊v⌋ - 1} : Finset ℤ)) :
    KernelTransform264.weight Δ (v + m) = 0 := by
  apply KernelTransform264.weight_zero hΔ hΔ1
  by_contra hn
  have habs : |v + (m : ℝ)| < 1 := lt_of_not_ge hn
  have hlo : (-1 : ℤ) ≤ ⌊v + (m : ℝ)⌋ := Int.le_floor.mpr (by norm_num; linarith [(abs_lt.mp habs).1])
  have hhi : ⌊v + (m : ℝ)⌋ < (1 : ℤ) := Int.floor_lt.mpr (by norm_num; exact (abs_lt.mp habs).2)
  rw [Int.floor_add_intCast] at hlo hhi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  omega

/-- P0082 page 356 Poisson display for the explicit kernel. Quadratic
decay and compact Fourier support verify Mathlib's summation hypotheses. -/
theorem poisson_kernel (Δ v α : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑' n : ℤ, (Kfun Δ (α + n) : ℂ) * eC (-((α + n) * v))) =
      eC (-(α * (⌊v⌋ : ℝ))) * (KernelTransform264.weight Δ (Int.fract v) : ℂ) +
        eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) *
          (KernelTransform264.weight Δ (Int.fract v - 1) : ℂ) := by
  classical
  let f : ℝ → ℂ := fun x => (Kfun Δ x : ℂ) * eC (-(x * v))
  let s : Finset ℤ := {-⌊v⌋, -⌊v⌋ - 1}
  have hf (m : ℤ) : 𝓕 f m = (KernelTransform264.weight Δ (v + m) : ℂ) :=
    fourier_modulated_kernel Δ v m hΔ hΔ1
  have hs (m : ℤ) (hm : m ∉ s) : 𝓕 f m = 0 := by
    rw [hf m, weight_integer_support Δ v hΔ hΔ1 m hm, Complex.ofReal_zero]
  have hsum : Summable (fun m : ℤ => 𝓕 f m) := summable_of_ne_finset_zero hs
  have hc : Continuous f := by
    dsimp [f]
    exact (KernelTransform264.Kfun_continuous Δ).mul (by unfold eC; fun_prop)
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc (by norm_num : (1 : ℝ) < 2)
    (modulated_kernel_isBigO Δ v hΔ hΔ1) hsum α
  change (∑' n : ℤ, f (α + n)) = _
  rw [hp, tsum_eq_sum (s := s) (fun m hm => by rw [hs m hm, zero_mul])]
  have hne : -⌊v⌋ ≠ -⌊v⌋ - 1 := by omega
  rw [show s = {-⌊v⌋, -⌊v⌋ - 1} from rfl, Finset.sum_pair hne]
  simp only [hf, fourier_coe_apply, Complex.ofReal_one, div_one]
  have h0 : v + ((-⌊v⌋ : ℤ) : ℝ) = Int.fract v := by
    simp only [Int.fract, Int.cast_neg, sub_eq_add_neg]
  have h1 : v + ((-⌊v⌋ - 1 : ℤ) : ℝ) = Int.fract v - 1 := by
    simp only [Int.fract, Int.cast_neg, Int.cast_sub, Int.cast_one]
    ring
  rw [h0, h1]
  have he0 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-⌊v⌋ : ℤ) : ℂ) * α) =
      eC (-(α * (⌊v⌋ : ℝ))) := by
    unfold eC
    push_cast
    congr 1
    ring
  have he1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-⌊v⌋ - 1 : ℤ) : ℂ) * α) =
      eC (-(α * ((⌊v⌋ + 1 : ℤ) : ℝ))) := by
    unfold eC
    push_cast
    congr 1
    ring
  rw [he0, he1]
  ring


end LeanLab.ExceptionalSet.Decomp404b
