/-
Finite endpoint integration for the zero counting interface.
The intended application is Gallagher 1970 p.336 before display 25.
The written argument was read from rendered source pages 333, 335 and 336.
Source https://doi.org/10.1007/BF01403187
AI wrote the Lean code. Codex task340. Goldbach is open.
-/
import LeanLab.Linnik.Decomp340a
import LeanLab.Linnik.Decomp340c
import LeanLab.Linnik.Decomp307b

open Finset MeasureTheory Complex
open scoped Classical
open LeanLab.Linnik.Decomp1532b LeanLab.Linnik.Decomp307b

namespace LeanLab.Linnik.Decomp340b

/-- Every natural power of a prime detector norm is integrable in the endpoint
with logarithmic weight on a compact positive interval. -/
theorem integrableOn_primeDetector_norm_pow_div {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x v : ℝ) (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ ^ k / y) (Set.Icc a b) := by
  simpa only [primeDetector, Nat.floor_natCast] using
    Decomp340a.integrableOn_floor_div
      (fun n : ℕ => ‖primeDetector χ x (n : ℝ) v‖ ^ k) (y := b) ha

/-- A supplied logarithmic L1 lower bound gives a squared detector lower bound.
This specializes the existing weighted Schwarz theorem and discharges its integrability inputs.
CONDITIONAL ON the supplied L1 bound. -/
theorem primeDetector_logarithmic_l2_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x B H : ℝ} (hx : 1 < x) (hB : 1 < B) (v : ℝ) (hH : 0 ≤ H)
    (hlower : H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    H ^ 2 / ((B - 1) * Real.log x) ≤
      ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ ^ 2 / y := by
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hmass : (∫ y in Set.Icc x (x ^ B), (1 : ℝ) / y) =
      (B - 1) * Real.log x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
    exact logarithmic_window_mass hx0 B
  have hw : ∀ᵐ y ∂volume.restrict (Set.Icc x (x ^ B)), 0 ≤ (1 : ℝ) / y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact div_nonneg (by norm_num) (hx0.trans_le hy.1).le
  have hwi : IntegrableOn (fun y : ℝ => (1 : ℝ) / y) (Set.Icc x (x ^ B)) := by
    exact (continuousOn_const.div continuousOn_id
      (by intro y hy; exact (hx0.trans_le hy.1).ne')).integrableOn_Icc
  have hfi : IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ * (1 / y))
      (Set.Icc x (x ^ B)) := by
    simpa only [pow_one, div_eq_mul_inv, one_mul] using
      integrableOn_primeDetector_norm_pow_div χ x v 1 hx0
  have hf2i : IntegrableOn (fun y : ℝ => ‖primeDetector χ x y v‖ ^ 2 * (1 / y))
      (Set.Icc x (x ^ B)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      integrableOn_primeDetector_norm_pow_div χ x v 2 hx0
  have hlower' : H ≤ ∫ y in Set.Icc x (x ^ B), ‖primeDetector χ x y v‖ * (1 / y) := by
    simpa only [div_eq_mul_inv, one_mul, intervalIntegral.integral_of_le hxy,
      integral_Icc_eq_integral_Ioc] using hlower
  have hh := detector_l2_of_l1 (volume.restrict (Set.Icc x (x ^ B)))
    (fun y => ‖primeDetector χ x y v‖) (fun y => 1 / y) hw hwi hfi hf2i
    (by rw [hmass]; exact mul_pos (by linarith) (Real.log_pos hx)) hH hlower'
  rw [hmass] at hh
  simpa only [div_eq_mul_inv, one_mul, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hxy] using hh

/-- The squared prime detector with logarithmic endpoint weight is integrable
on each compact endpoint and height rectangle with positive endpoint lower bound. -/
theorem integrableOn_primeDetector_energy_rectangle {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) {a b U V : ℝ} (ha : 0 < a) :
    IntegrableOn (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1)
      (Set.Icc a b ×ˢ Set.Icc U V) := by
  let M : ℝ := ∑ n ∈ Icc 1 ⌊b⌋₊, ‖(Real.log n / (n : ℝ) : ℂ)‖
  have hbound (y v : ℝ) (hy : y ≤ b) : ‖primeDetector χ x y v‖ ≤ M := by
    unfold primeDetector
    calc
      _ ≤ ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log n / (n : ℝ) : ℂ) * χ n *
            Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          ‖(Real.log n / (n : ℝ) : ℂ)‖ := by
        apply sum_le_sum
        intro n hn
        have he : ‖Complex.exp (-((Real.log n * v : ℝ) : ℂ) * I)‖ = 1 := by
          rw [Complex.norm_exp]
          norm_num only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, zero_mul, mul_one, sub_zero, neg_zero, Real.exp_zero]
        rw [norm_mul, norm_mul, he, mul_one]
        exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
      _ ≤ M := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, hp⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hn).1; omega,
            (mem_Ioc.mp hn).2.trans (Nat.floor_le_floor hy)⟩
        · intro n _ _
          exact norm_nonneg _
  have hm : Measurable (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1) :=
    ((measurable_primeDetector_uncurry χ x).norm.pow_const 2).div measurable_fst
  apply IntegrableOn.of_bound (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    hm.aestronglyMeasurable (M ^ 2 / a)
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  have hz0 : 0 < z.1 := ha.trans_le hz.1.1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hz0.le)]
  exact (div_le_div_of_nonneg_left (sq_nonneg _) ha hz.1.1).trans
    (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hbound z.1 z.2 hz.1.2) 2) ha.le)

/-- The endpoint and height integrations in the detector energy commute.
The finite rectangle integrability theorem discharges the Fubini hypothesis. -/
theorem primeDetector_energy_swap {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    {a b U V : ℝ} (ha : 0 < a) (hab : a ≤ b) (hUV : U ≤ V) :
    (∫ v in U..V, ∫ y in a..b, ‖primeDetector χ x y v‖ ^ 2 / y) =
      ∫ y in a..b, (∫ v in U..V, ‖primeDetector χ x y v‖ ^ 2) / y := by
  have hi : IntegrableOn
      (Function.uncurry (fun y v : ℝ => ‖primeDetector χ x y v‖ ^ 2 / y))
      (Set.uIoc a b ×ˢ Set.uIoc U V) := by
    apply (integrableOn_primeDetector_energy_rectangle χ x ha).mono_set
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le hUV]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  simpa only [intervalIntegral.integral_div] using
    (intervalIntegral_intervalIntegral_swap hi).symm

/-- The logarithmically weighted squared detector integral is integrable
as a function of height on each compact height interval. -/
theorem integrableOn_primeDetector_height_energy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) {a b U V : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun v : ℝ => ∫ y in a..b, ‖primeDetector χ x y v‖ ^ 2 / y)
      (Set.Icc U V) := by
  have hi := integrableOn_primeDetector_energy_rectangle χ x (U := U) (V := V) (b := b) ha
  have hp : Integrable (fun z : ℝ × ℝ => ‖primeDetector χ x z.1 z.2‖ ^ 2 / z.1)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc U V))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hi
  simpa only [IntegrableOn, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab] using hp.integral_prod_right

/-- A finite height family with local occupancy and logarithmic L1 detection
is controlled by the averaged squared prime detector energy.
All integrability and interchange premises are discharged here.
CONDITIONAL ON the supplied occupancy and detector lower bounds. -/
theorem finite_height_count_from_log_detector {ι : Type*} (S : Finset ι)
    (height : ι → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {T r x B H L : ℝ} (hr : 0 < r) (hrT : r ≤ T)
    (hx : 1 < x) (hB : 1 < B) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hheight : ∀ i ∈ S, height i ∈ Set.Icc (-T) T)
    (hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ L)
    (hdetect : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    (S.card : ℝ) * r * H ^ 2 ≤ L * ((B - 1) * Real.log x) *
      (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hTT : -T ≤ T := by linarith
  have hmass : 0 < (B - 1) * Real.log x :=
    mul_pos (by linarith) (Real.log_pos hx)
  let g : ℝ → ℝ := fun v => ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ ^ 2 / y
  have hg : IntegrableOn g (Set.Icc (-T) T) :=
    integrableOn_primeDetector_height_energy χ x hx0 hxy
  have hg0 : ∀ v ∈ Set.Icc (-T) T, 0 ≤ g v := by
    intro v hv
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (sq_nonneg _) (hx0.trans_le hy.1).le
  have hd : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) →
      H ^ 2 / ((B - 1) * Real.log x) ≤ g v := by
    intro i hi v hv hvi
    exact primeDetector_logarithmic_l2_lower χ hx hB v hH (hdetect i hi v hv hvi)
  have hh := finite_height_count_from_local_detector S height hr hrT
    (div_nonneg (sq_nonneg H) hmass.le) hL hheight g hg hg0 hlocal hd
  have hh' : ((S.card : ℝ) * r * H ^ 2) / ((B - 1) * Real.log x) ≤
      L * ∫ v in Set.Icc (-T) T, g v := by
    convert hh using 1 <;> ring
  have hmul := (div_le_iff₀ hmass).mp hh'
  calc
    _ ≤ (L * ∫ v in Set.Icc (-T) T, g v) * ((B - 1) * Real.log x) := hmul
    _ = L * ((B - 1) * Real.log x) * (∫ v in (-T)..T, g v) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTT]
      ring
    _ = _ := by rw [primeDetector_energy_swap χ x hx0 hxy hTT]

/-- A fixed nonprincipal primitive character in a narrow strip satisfies the
integrated count bound once its local L1 detector lower bound is supplied.
The conductor sum, principal low heights and uniform parameter assembly are absent.
CONDITIONAL ON the supplied local L1 detector. -/
theorem nonprincipal_zero_count_from_local_l1 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      ∀ x B r H : ℝ, 1 < x → 1 < B → 0 < r →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H →
      (∀ v : ℝ, |v| ≤ T →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
        H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) →
      (zeroCount χ (1 - r) T : ℝ) * H ^ 2 ≤
        C * Real.log T * ((B - 1) * Real.log x) *
          (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  obtain ⟨C, hC, hocc⟩ := Decomp340c.primitive_height_window_occupancy
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hp hχ x B r H hx hB hr hrlo hrhi hH hdetect
  obtain ⟨S, hS, hcard⟩ := Decomp340c.exists_zeroCount_finset χ hp
    (show 1 / 2 ≤ 1 - r by linarith) (show 0 ≤ T by linarith)
  have hstrip (ρ : ℂ) (hρ : ρ ∈ S) :
      χ.LFunction ρ = 0 ∧ 1 - r ≤ ρ.re ∧ ρ.re ≤ 1 := by
    obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρ
    refine ⟨hz, hβ, le_of_lt ?_⟩
    by_contra hn
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_not_gt hn) hz
  have hheight : ∀ ρ ∈ S, ρ.im ∈ Set.Icc (-T) T := by
    intro ρ hρ
    exact abs_le.mp ((hS ρ).mp hρ).2.2
  have hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
    intro v hv
    exact hocc T hT q hqT χ hp v r (abs_le.mpr hv)
      (fun he => (hχ he).elim) hrlo hrhi S hstrip
  have hd : ∀ ρ ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (ρ.im - r) (ρ.im + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
    intro ρ hρ v hv hρv
    obtain ⟨hz, hβlo, hβhi⟩ := hstrip ρ hρ
    apply hdetect v (abs_le.mpr hv)
    refine ⟨ρ, hz, ?_⟩
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hρv.2], by linarith [hρv.1]⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have hh := finite_height_count_from_log_detector S (fun ρ => ρ.im) χ hr
    (show r ≤ T by linarith) hx hB hH
    (mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))) hheight hlocal hd
  rw [hcard] at hh
  apply (mul_le_mul_iff_left₀ hr).mp
  convert hh using 1 <;> ring

/-- Principal zeros above absolute height three satisfy the same finite
integrated counting estimate. The principal height exclusion is discharged by geometry.
CONDITIONAL ON the supplied local L1 detector. Gallagher p.336 before display 25. -/
theorem principal_high_count_from_local_l1 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T x B r H : ℝ, 2 ≤ T → 1 < x → 1 < B → 0 < r →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H →
      ∀ S : Finset ℂ,
      (∀ ρ ∈ S, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
        1 - r ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 3 ≤ |ρ.im| ∧ |ρ.im| ≤ T) →
      (∀ v : ℝ, |v| ≤ T → 2 ≤ |v| →
        (∃ ρ : ℂ, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
          ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
        H ≤ ∫ y in x..(x ^ B), ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ / y) →
      (S.card : ℝ) * H ^ 2 ≤ C * Real.log T * ((B - 1) * Real.log x) *
        (∫ y in x..(x ^ B),
          (∫ v in (-T)..T, ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ ^ 2) / y) := by
  obtain ⟨C, hC, hocc⟩ := Decomp340c.primitive_height_window_occupancy
  refine ⟨C, hC, ?_⟩
  intro T x B r H hT hx hB hr hrlo hrhi hH S hS hdetect
  have hstrip : ∀ ρ ∈ S, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
      1 - r ≤ ρ.re ∧ ρ.re ≤ 1 := by
    intro ρ hρ
    obtain ⟨hz, hlo, hhi, h3, hγ⟩ := hS ρ hρ
    exact ⟨hz, hlo, hhi⟩
  have hheight : ∀ ρ ∈ S, ρ.im ∈ Set.Icc (-T) T := by
    intro ρ hρ
    exact abs_le.mp (hS ρ hρ).2.2.2.2
  have hvlarge (ρ : ℂ) (hρ : ρ ∈ S) (v : ℝ)
      (hvρ : v ∈ Set.Icc (ρ.im - r) (ρ.im + r)) : 2 ≤ |v| := by
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hvρ.2], by linarith [hvρ.1]⟩
    have htri : |ρ.im| ≤ |ρ.im - v| + |v| := by
      simpa only [sub_add_cancel] using abs_add_le (ρ.im - v) v
    have h3 := (hS ρ hρ).2.2.2.1
    linarith
  have hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
    intro v hv
    by_cases hex : ∃ ρ ∈ S, v ∈ Set.Icc (ρ.im - r) (ρ.im + r)
    · obtain ⟨ρ, hρ, hvρ⟩ := hex
      exact hocc T hT 1 (by norm_num; linarith) 1 DirichletCharacter.isPrimitive_one_level_one
        v r (abs_le.mpr hv) (fun _ => hvlarge ρ hρ v hvρ) hrlo hrhi S hstrip
    · have hz : (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
          (fun _ => (1 : ℝ)) v) = 0 := by
        apply sum_eq_zero
        intro ρ hρ
        exact Set.indicator_of_notMem (fun hvρ => hex ⟨ρ, hρ, hvρ⟩) _
      rw [hz]
      exact mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))
  have hd : ∀ ρ ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (ρ.im - r) (ρ.im + r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector (1 : DirichletCharacter ℂ 1) x y v‖ / y := by
    intro ρ hρ v hv hvρ
    obtain ⟨hz, hlo, hhi⟩ := hstrip ρ hρ
    apply hdetect v (abs_le.mpr hv) (hvlarge ρ hρ v hvρ)
    refine ⟨ρ, hz, ?_⟩
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hvρ.2], by linarith [hvρ.1]⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have hh := finite_height_count_from_log_detector S (fun ρ => ρ.im)
    (1 : DirichletCharacter ℂ 1) hr (show r ≤ T by linarith) hx hB hH
    (mul_nonneg (mul_nonneg hC hr.le) (Real.log_nonneg (by linarith))) hheight hlocal hd
  apply (mul_le_mul_iff_left₀ hr).mp
  convert hh using 1 <;> ring

/-- Gallagher 1970 p.336 fixed character counting with the bounded principal
low height term retained at modulus one. The supplied detector is used only locally.
CONDITIONAL ON the supplied local L1 detector. -/
theorem primitive_count_from_local_l1 : ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
    ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ x B r H σ : ℝ, 1 < x → 1 < B → 0 < r →
    1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 → 0 ≤ H → 1 - r ≤ σ →
    (∀ v : ℝ, |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) →
    (zeroCount χ σ T : ℝ) * H ^ 2 ≤ (if q = 1 then D else 0) * H ^ 2 +
      A * Real.log T * ((B - 1) * Real.log x) *
        (∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y) := by
  obtain ⟨Aₙ, hAₙ, hnp⟩ := nonprincipal_zero_count_from_local_l1
  obtain ⟨Aₚ, hAₚ, hpr⟩ := principal_high_count_from_local_l1
  obtain ⟨D, hD, hlow⟩ := principal_low_height_zero_count
  refine ⟨max Aₙ Aₚ, D, le_max_of_le_left hAₙ, hD, ?_⟩
  intro T hT q hq hqT χ hp x B r H σ hx hB hr hrlo hrhi hH hσ hdetect
  have hσr : 1 / 2 ≤ 1 - r := by linarith
  have hσ0 : 1 / 2 ≤ σ := hσr.trans hσ
  have hT0 : 0 ≤ T := by linarith
  have hx0 : 0 < x := by linarith
  have hxy : x ≤ x ^ B := by simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  let E : ℝ := ∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg
      (intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _))
      (hx0.trans_le hy.1).le
  have hcoef : 0 ≤ Real.log T * ((B - 1) * Real.log x) * E :=
    mul_nonneg (mul_nonneg (Real.log_nonneg (by linarith))
      (mul_nonneg (by linarith) (Real.log_pos hx).le)) hE
  have hAn : Aₙ * Real.log T * ((B - 1) * Real.log x) * E ≤
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E := by
    convert mul_le_mul_of_nonneg_right (le_max_left Aₙ Aₚ) hcoef using 1 <;> ring
  have hAp : Aₚ * Real.log T * ((B - 1) * Real.log x) * E ≤
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E := by
    convert mul_le_mul_of_nonneg_right (le_max_right Aₙ Aₚ) hcoef using 1 <;> ring
  by_cases hq1 : q = 1
  · subst q
    have heχ : χ = 1 := Subsingleton.elim _ _
    subst χ
    obtain ⟨S, hS, hcard⟩ := Decomp340c.exists_zeroCount_finset (1 : DirichletCharacter ℂ 1) hp hσ0 hT0
    let Sh := S.filter (fun ρ => 3 ≤ |ρ.im|)
    let Sl := S.filter (fun ρ => |ρ.im| ≤ 3)
    have hsub : S ⊆ Sh ∪ Sl := by
      intro ρ hρ
      by_cases hh : 3 ≤ |ρ.im|
      · exact mem_union_left _ (mem_filter.mpr ⟨hρ, hh⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hρ, (lt_of_not_ge hh).le⟩)
    have hcardle : (S.card : ℝ) ≤ (Sh.card : ℝ) + Sl.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le Sh Sl)
    obtain ⟨S₃, hS₃, hc₃⟩ := Decomp340c.exists_zeroCount_finset (1 : DirichletCharacter ℂ 1) hp hσ0
      (by norm_num : (0 : ℝ) ≤ 3)
    have hSl : Sl ⊆ S₃ := by
      intro ρ hρ
      obtain ⟨hρS, hρ3⟩ := mem_filter.mp hρ
      obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρS
      exact (hS₃ ρ).mpr ⟨hz, hβ, hρ3⟩
    have hlowcard : (Sl.card : ℝ) ≤ D := by
      have hh : (Sl.card : ℝ) ≤ zeroCount (1 : DirichletCharacter ℂ 1) σ 3 := by
        rw [← hc₃]
        exact_mod_cast card_le_card hSl
      exact hh.trans (hlow σ hσ0)
    have hmem : ∀ ρ ∈ Sh, (1 : DirichletCharacter ℂ 1).LFunction ρ = 0 ∧
        1 - r ≤ ρ.re ∧ ρ.re ≤ 1 ∧ 3 ≤ |ρ.im| ∧ |ρ.im| ≤ T := by
      intro ρ hρ
      obtain ⟨hρS, h3⟩ := mem_filter.mp hρ
      obtain ⟨hz, hβ, hγ⟩ := (hS ρ).mp hρS
      refine ⟨hz, hσ.trans hβ, ?_, h3, hγ⟩
      by_contra hn
      rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_ge hn) hz
    have hh := hpr T x B r H hT hx hB hr hrlo hrhi hH Sh hmem
      (fun v hv hv2 hz => hdetect v hv (fun _ => hv2) hz)
    change (zeroCount (1 : DirichletCharacter ℂ 1) σ T : ℝ) * H ^ 2 ≤ D * H ^ 2 +
      max Aₙ Aₚ * Real.log T * ((B - 1) * Real.log x) * E
    rw [← hcard]
    have hh' := hh.trans hAp
    have hm := mul_le_mul_of_nonneg_right hcardle (sq_nonneg H)
    have hlm := mul_le_mul_of_nonneg_right hlowcard (sq_nonneg H)
    nlinarith
  · have hχ : χ ≠ 1 := by
      intro he
      apply hq1
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, he, DirichletCharacter.conductor_one] at hh
      exact hh.symm
    obtain ⟨S₀, hS₀, hc₀⟩ := Decomp340c.exists_zeroCount_finset χ hp hσr hT0
    have hsub : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} ⊆ (S₀ : Set ℂ) := by
      intro ρ hρ
      exact (hS₀ ρ).mpr ⟨hρ.1, hσ.trans hρ.2.1, hρ.2.2⟩
    have hmono : (zeroCount χ σ T : ℝ) ≤ zeroCount χ (1 - r) T := by
      have hh := Set.ncard_le_ncard hsub S₀.finite_toSet
      rw [Set.ncard_coe_finset, hc₀] at hh
      exact_mod_cast hh
    have hh := hnp T hT q hqT χ hp hχ x B r H hx hB hr hrlo hrhi hH
      (fun v hv hz => hdetect v hv (fun he => (hχ he).elim) hz)
    simp only [hq1, ite_false, zero_mul, zero_add]
    exact (mul_le_mul_of_nonneg_right hmono (sq_nonneg H)).trans (hh.trans hAn)

/-- The finite primitive character sum can be moved through the endpoint integral.
The positive modulus convention agrees exactly with detectorEnergy. -/
theorem integral_detectorEnergy_eq_sum (T a : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∫ u in x..y, detectorEnergy T a u / u) =
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          ∫ u in x..y, (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u := by
  have hid (u : ℝ) : detectorEnergy T a u =
      ∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          ∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2 := by
    unfold detectorEnergy
    symm
    apply sum_bij (fun q _ => q + 1)
    · intro q hq
      have hh := mem_range.mp hq
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro q hq q' hq' he
      omega
    · intro q hq
      have hh := mem_Icc.mp hq
      exact ⟨q - 1, mem_range.mpr (by omega), by omega⟩
    · intro q hq
      rfl
  have hi {q : ℕ} (χ : DirichletCharacter ℂ q) :
      IntervalIntegrable (fun u : ℝ => (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u)
        volume x y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
    simpa only [primeDetector, Nat.floor_natCast] using
      Decomp340a.integrableOn_floor_div
        (fun n : ℕ => ∫ v in (-T)..T, ‖primeDetector χ a (n : ℝ) v‖ ^ 2) (y := y) hx
  simp_rw [hid, sum_div]
  have hiq (q : ℕ) : IntervalIntegrable
      (fun u : ℝ => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter
        (fun χ => χ.IsPrimitive), (∫ v in (-T)..T, ‖primeDetector χ a u v‖ ^ 2) / u)
      volume x y := by
    convert IntervalIntegrable.sum
      ((univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive))
      (fun χ hχ => hi χ) using 1
    ext u
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum (fun q hq => hiq q)]
  apply sum_congr rfl
  intro q hq
  exact intervalIntegral.integral_finsetSum (fun χ hχ => hi χ)

/-- Gallagher 1970 p.336 the fixed character integrated counting inequality
before display 25. This is restricted to large T and a fixed narrow strip.
The principal low height contribution is retained only at modulus one.
There is no conductor or character sum in this leaf. -/
theorem fixed_character_narrow_count_from_detector
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    ∃ K B c C D η T₀ : ℝ,
      5 ≤ K ∧ 1 < B ∧ 0 < c ∧ 0 ≤ C ∧ 0 ≤ D ∧
      0 < η ∧ η ≤ 1 / 16 ∧ 2 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
        (zeroCount χ σ T : ℝ) ≤ (if q = 1 then D else 0) +
          C * T ^ (c * (1 - σ)) *
            (∫ y in (T ^ K)..((T ^ K) ^ B),
              (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
            Real.log T ^ 2 := by
  obtain ⟨r₀, A, B, C₀, c₀, hr₀, hr₀hi, hA, hB, hC₀, hc₀, hdet⟩ := hdetector
  obtain ⟨M, D, hM, hD, hcount⟩ := primitive_count_from_local_l1
  let K : ℝ := max A 5
  let η : ℝ := min (r₀ / 2) (1 / 16)
  let T₀ : ℝ := Real.exp (1 / η)
  let C : ℝ := M * (B - 1) / (c₀ ^ 2 * K ^ 3) * Real.exp (2 * C₀ * K)
  have hK : 5 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηhi : η ≤ 1 / 16 := min_le_right _ _
  have hηr : η ≤ r₀ / 2 := min_le_left _ _
  have hηinv : (1 : ℝ) ≤ 1 / η := by
    apply (le_div_iff₀ hη).mpr
    linarith
  have hT₀ : 2 ≤ T₀ := by
    dsimp [T₀]
    linarith [Real.add_one_le_exp (1 / η)]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K, B, 4 * C₀ * K, C, D, η, T₀, hK, hB, by positivity, hC,
    hD, hη, hηhi, hT₀, ?_⟩
  intro T hlarge σ hσn hσ1 q hq hqT χ hp
  have hT : 2 ≤ T := hT₀.trans hlarge
  have hT0 : 0 < T := by linarith
  let l : ℝ := Real.log T
  let d : ℝ := 1 - σ
  let p : ℝ := 1 / (2 * l)
  let r : ℝ := max d p
  let x : ℝ := T ^ K
  let H : ℝ := c₀ * Real.exp (-2 * C₀ * K * r * l) * (K * l) ^ 2
  let E : ℝ := ∫ y in x..(x ^ B), (∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2) / y
  let N : ℝ := (zeroCount χ σ T : ℝ)
  let Dq : ℝ := if q = 1 then D else 0
  have hl : 0 < l := Real.log_pos (by linarith)
  have hd : 0 < d := by dsimp [d]; linarith
  have hdη : d ≤ η := by dsimp [d]; linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hlogη : 1 / η ≤ l := by
    have hh := Real.log_le_log (Real.exp_pos (1 / η)) hlarge
    simpa only [l, T₀, Real.log_exp] using hh
  have hηl : 1 ≤ l * η := (div_le_iff₀ hη).mp hlogη
  have hpη : p ≤ η := by
    dsimp [p]
    apply (div_le_iff₀ (show 0 < 2 * l by positivity)).mpr
    nlinarith
  have hr : 0 < r := hp0.trans_le (le_max_right _ _)
  have hrη : r ≤ η := max_le hdη hpη
  have hp_id : 2 * p = 1 / l := by dsimp [p]; field_simp
  have hrlo : 1 / Real.log T ≤ 2 * r := by
    change 1 / l ≤ 2 * r
    have hh : p ≤ r := le_max_right _ _
    linarith
  have hrhi : 2 * r ≤ 1 / 8 := by linarith
  have hrr₀ : 2 * r ≤ r₀ := by linarith
  have hrpad : r ≤ d + 1 / (2 * l) := by
    change max d p ≤ d + p
    exact max_le (by linarith) (by linarith)
  have hσr : 1 - r ≤ σ := by
    have hh : d ≤ r := le_max_left _ _
    dsimp [d] at hh
    linarith
  have hx : 1 < x := Real.one_lt_rpow (by linarith) hK0
  have hx0 : 0 < x := by linarith
  have hxA : T ^ A ≤ x :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hlogx : Real.log x = K * l := by
    dsimp [x, l]
    exact Real.log_rpow hT0 K
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hH_eq : H = c₀ * x ^ (-C₀ * (2 * r)) * Real.log x ^ 2 := by
    dsimp [H]
    rw [Real.rpow_def_of_pos hx0, hlogx]
    have he : (K * l) * (-C₀ * (2 * r)) = -2 * C₀ * K * r * l := by ring
    rw [he]
  have hdet' : ∀ v : ℝ, |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r) →
      H ≤ ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y := by
    intro v hv hχ hz
    rw [hH_eq]
    apply hdet T hT q hqT χ v (2 * r) hv hχ hrlo hrr₀
    · obtain ⟨ρ, hρ, hnorm⟩ := hz
      exact ⟨ρ, hρ, by simpa only [mul_comm] using hnorm⟩
    · exact hxA
  have hxy : x ≤ x ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx.le hB.le
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _))
      (hx0.trans_le hy.1).le
  change N ≤ Dq + C * T ^ ((4 * C₀ * K) * (1 - σ)) * E / Real.log T ^ 2
  by_cases hsmall : N ≤ Dq
  · exact hsmall.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT0.le _)) hE) (sq_nonneg _)))
  · have hn : 0 ≤ N - Dq := by linarith
    have hraw := hcount T hT q hqT χ hp x B r H σ hx hB hr hrlo hrhi hH hσr hdet'
    change N * H ^ 2 ≤ Dq * H ^ 2 + M * l * ((B - 1) * Real.log x) * E at hraw
    rw [hlogx] at hraw
    have hraw' : (N - Dq) * (c₀ * Real.exp (-2 * C₀ * K * r * l) * (K * l) ^ 2) ^ 2 ≤
        M * l * ((B - 1) * K * l) * E := by
      change (N - Dq) * H ^ 2 ≤ M * l * ((B - 1) * K * l) * E
      nlinarith only [hraw]
    have hs := LeanLab.Linnik.Decomp340a.detector_count_scale hn hc₀ hC₀.le hK0 hl hrpad hraw'
    have hpow : Real.exp (4 * C₀ * K * d * l) = T ^ ((4 * C₀ * K) * (1 - σ)) := by
      rw [Real.rpow_def_of_pos hT0]
      dsimp [d, l]
      congr 1
      ring
    rw [hpow] at hs
    change N - Dq ≤ C * T ^ ((4 * C₀ * K) * (1 - σ)) * E / Real.log T ^ 2 at hs
    linarith only [hs]


/-- Gallagher 1970 p.336 Theorem 6 counting assembly before display 25.
Exact statement of the sealed integrated counting target.
CONDITIONAL ON the detector supplied in the exact sealed statement only.
This assembly has no proof hole of its own. -/
theorem zero_count_from_integrated_detector
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    ∀ b : ℝ, 0 < b → ∃ K B c C : ℝ, 5 ≤ K ∧ 1 < B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
      (∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ)) ≤
        C * T ^ (c * (1 - σ)) *
          (1 + (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
            Real.log T ^ 2) := by
  obtain ⟨K, B, c, C, D, η, T₀, hK, hB, hc, hC, hD, hη, hηhi, hT₀, hfixed⟩ :=
    fixed_character_narrow_count_from_detector hdetector
  obtain ⟨P, hP, hpoly⟩ := density_sum_polynomial
  obtain ⟨W, hW, hwide⟩ := density_sum_fixed_gap η hη
  intro b hb
  let c' : ℝ := max c (4 / η)
  let C' : ℝ := D + P * T₀ ^ 4 + W + C
  have hc' : 0 < c' := hc.trans_le (le_max_left _ _)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨K, B, c', C', hK, hB, hc', hC', ?_⟩
  intro T hT σ hσ hσb
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hσ1 : σ < 1 := by linarith [div_pos hb hl]
  have hδ : 0 ≤ 1 - σ := by linarith
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow hT1 (by linarith)
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hxy : T ^ K ≤ (T ^ K) ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  let E : ℝ := ∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y
  let Z : ℝ := E / Real.log T ^ 2
  let N : ℝ := ∑ q ∈ range ⌊T⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
      (zeroCount χ σ T : ℝ)
  change N ≤ C' * T ^ (c' * (1 - σ)) * (1 + Z)
  have hE : 0 ≤ E := by
    apply intervalIntegral.integral_nonneg hxy
    intro y hy
    exact div_nonneg (detectorEnergy_nonneg hT0.le _ _) (hx0.trans_le hy.1).le
  have hZ : 0 ≤ Z := div_nonneg hE (sq_nonneg _)
  have htp : 1 ≤ T ^ (c' * (1 - σ)) :=
    Real.one_le_rpow hT1 (mul_nonneg hc'.le hδ)
  have htp0 : 0 ≤ T ^ (c' * (1 - σ)) := Real.rpow_nonneg hT0.le _
  have hbase : C' * T ^ (c' * (1 - σ)) ≤
      C' * T ^ (c' * (1 - σ)) * (1 + Z) :=
    le_mul_of_one_le_right (mul_nonneg hC' htp0) (by linarith)
  have hCtp : C' ≤ C' * T ^ (c' * (1 - σ)) := le_mul_of_one_le_right hC' htp
  have hDP : D ≤ C' ∧ P * T₀ ^ 4 ≤ C' ∧ W ≤ C' ∧ C ≤ C' := by
    dsimp [C']
    have hPT : 0 ≤ P * T₀ ^ 4 := mul_nonneg hP (by positivity)
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  by_cases hlarge : T₀ ≤ T
  · by_cases hnarrow : 1 - η ≤ σ
    · have hfloor : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff _).mpr hT1
      have hzero : 0 ∈ range ⌊T⌋₊ := mem_range.mpr (by omega)
      have hprincipal :
          (∑ q ∈ range ⌊T⌋₊,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
              (if q + 1 = 1 then D else 0)) ≤ D := by
        rw [sum_eq_single_of_mem 0 hzero]
        · simp only [Nat.zero_add, ite_true]
          have hcard : Fintype.card (DirichletCharacter ℂ 1) = 1 := by
            rw [← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
            norm_num
          calc
            _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ 1)), D :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hD)
            _ = D := by simp [hcard]
        · intro q hq hq0
          have hne : q + 1 ≠ 1 := by omega
          simp only [hne, ite_false, sum_const_zero]
      have hsumE :
          (∑ q ∈ range ⌊T⌋₊,
            ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
              ∫ y in (T ^ K)..((T ^ K) ^ B),
                (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) = E :=
        (integral_detectorEnergy_eq_sum T (T ^ K) hx0 hxy).symm
      have hcount : N ≤ D + C * T ^ (c * (1 - σ)) * Z := by
        calc
          N ≤ ∑ q ∈ range ⌊T⌋₊,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
                ((if q + 1 = 1 then D else 0) + C * T ^ (c * (1 - σ)) *
                  (∫ y in (T ^ K)..((T ^ K) ^ B),
                    (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
                    Real.log T ^ 2) := by
            apply sum_le_sum
            intro q hq
            apply sum_le_sum
            intro χ hχ
            have hqT : ((q + 1 : ℕ) : ℝ) ≤ T :=
              (show ((q + 1 : ℕ) : ℝ) ≤ ⌊T⌋₊ by
                exact_mod_cast (show q + 1 ≤ ⌊T⌋₊ by have := mem_range.mp hq; omega)).trans
                (Nat.floor_le hT0.le)
            exact hfixed T hlarge σ hnarrow hσ1 (q + 1) hqT χ (mem_filter.mp hχ).2
          _ = (∑ q ∈ range ⌊T⌋₊,
              ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
                (if q + 1 = 1 then D else 0)) +
              C * T ^ (c * (1 - σ)) *
                (∑ q ∈ range ⌊T⌋₊,
                  ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
                    ∫ y in (T ^ K)..((T ^ K) ^ B),
                      (∫ v in (-T)..T, ‖primeDetector χ (T ^ K) y v‖ ^ 2) / y) /
                        Real.log T ^ 2 := by
            simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_mul, mul_assoc]
          _ ≤ D + C * T ^ (c * (1 - σ)) * Z := by
            rw [hsumE]
            simp only [Z, div_eq_mul_inv, mul_assoc]
            exact add_le_add hprincipal le_rfl
      have hp : T ^ (c * (1 - σ)) ≤ T ^ (c' * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hT1
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)
      calc
        N ≤ D + C * T ^ (c * (1 - σ)) * Z := hcount
        _ ≤ C' * T ^ (c' * (1 - σ)) + C' * T ^ (c' * (1 - σ)) * Z :=
          add_le_add (hDP.1.trans hCtp)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul hDP.2.2.2 hp (Real.rpow_nonneg hT0.le _) hC') hZ)
        _ = _ := by ring
    · have hw : N ≤ W * T ^ ((4 / η) * (1 - σ)) :=
        hwide T hT σ (by linarith) (le_of_not_ge hnarrow)
      have hp : T ^ ((4 / η) * (1 - σ)) ≤ T ^ (c' * (1 - σ)) :=
        Real.rpow_le_rpow_of_exponent_le hT1
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ)
      exact hw.trans ((mul_le_mul_of_nonneg_left hp hW).trans
        ((mul_le_mul_of_nonneg_right hDP.2.2.1 htp0).trans hbase))
  · have hpoly' : N ≤ P * T ^ (4 : ℕ) := hpoly T hT σ (by linarith)
    have hp : T ^ (4 : ℕ) ≤ T₀ ^ 4 :=
      pow_le_pow_left₀ hT0.le (lt_of_not_ge hlarge).le 4
    exact hpoly'.trans ((mul_le_mul_of_nonneg_left hp hP).trans
      (hDP.2.1.trans (hCtp.trans hbase)))

/-- Gallagher 1970 p.336 Theorem 6 display 24.
Exact density transition from the clean integrated counting supply and the rough hybrid energy.
CONDITIONAL ON the supplied detector and rough hybrid bound. -/
theorem gallagher_density_from_detector_and_prime_hybrid
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y)
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  intro b hb
  obtain ⟨K, B, c, C, hK, hB, hc, hC, hcount⟩ := zero_count_from_integrated_detector hdetector b hb
  obtain ⟨H, hH, henergy⟩ := integrated_detector_energy_of_prime_hybrid hprime K B hK hB
  refine ⟨c, C * (1 + H), hc, by positivity, ?_⟩
  intro T hT σ hσ hσb
  have hl : 0 < Real.log T ^ 2 := sq_pos_of_pos (Real.log_pos (by linarith))
  have he : (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
      Real.log T ^ 2 ≤ H := (div_le_iff₀ hl).mpr (henergy T hT)
  calc
    _ ≤ C * T ^ (c * (1 - σ)) *
        (1 + (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
          Real.log T ^ 2) := hcount T hT σ hσ hσb
    _ ≤ C * T ^ (c * (1 - σ)) * (1 + H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring


end LeanLab.Linnik.Decomp340b
