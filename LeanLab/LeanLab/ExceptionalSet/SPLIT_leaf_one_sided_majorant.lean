import LeanLab.ExceptionalSet.Decomp523a

/-!
Split of the one sided trigonometric majorant input of `Decomp523a`.

`leaf_one_sided_majorant` asks for an absolute constant plus, for every half
open interval and cutoff, a constant coefficient and a family of coefficients
with three properties.  This file keeps that statement, name for name, as
`leaf_one_sided_majorant_split`, and moves its content into three concrete
leaves whose coefficients are written out in full, together with the
elementary cutoff one case, which the assembly itself proves.

* `leaf_fejer_convolution_majorant`: the squared exponential sum of the cutoff
  is the Fejer kernel; its mass on a short arc is bounded below, so the
  smoothed periodic indicator of the slightly enlarged interval dominates the
  interval indicator.
* `leaf_fejer_sum_representation`: the finite Fourier expansion identity, which
  turns the weighted cosine sum into the smoothed indicator minus its mean.
* `leaf_fourier_coefficient_le`: the k-th Fourier coefficient of a periodic
  interval indicator is at most one over pi k, which bounds the weights.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-! ## Private helpers for the Fourier coefficient bound -/

/-- Norm of a real number seen in `ℂ`. -/
private lemma norm_real_cast (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- Norm of the imaginary unit. -/
private lemma norm_I_one : ‖Complex.I‖ = 1 := by simp

/-- `eC` has unit modulus. -/
private lemma norm_eC_one (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have h : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- Bound on the modulus of the frequency factor `2 * pi * I * k`. -/
private lemma norm_two_pi_I_mul (k : ℕ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))‖ = 2 * Real.pi * (k : ℝ) := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) =
      ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, norm_mul, norm_I_one, mul_one, norm_real_cast, abs_of_nonneg (by positivity)]

/-- Continuity of the phase function. -/
private lemma continuous_eC_neg_mul (k : ℕ) : Continuous fun y : ℝ => eC (-((k : ℝ) * y)) := by
  unfold eC
  fun_prop

/-- The phase has an exponential form of the expected shape. -/
private lemma eC_neg_mul_eq_exp (k : ℕ) (y : ℝ) :
    eC (-((k : ℝ) * y)) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * y : ℝ) : ℂ)) := by
  unfold eC
  congr 1
  push_cast
  ring

/-- Derivative of the phase. -/
private lemma hasDerivAt_eC_neg_mul (k : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => eC (-((k : ℝ) * z)))
      (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y))) y := by
  have h1 : HasDerivAt (fun z : ℝ => (((-(k : ℝ)) * z : ℝ) : ℂ)) (((-(k : ℝ)) : ℝ) : ℂ) y := by
    have hbase := ((hasDerivAt_id (x := y)).const_mul (-(k : ℝ))).ofReal_comp
    simpa using hbase
  have h2 : HasDerivAt (fun z : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * z : ℝ) : ℂ))
      ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) : ℝ) : ℂ)) y := h1.const_mul _
  have h3 := h2.cexp
  have hfun : (fun z : ℝ => eC (-((k : ℝ) * z))) =
      (fun x : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * x : ℝ) : ℂ))) := by
    funext z
    exact eC_neg_mul_eq_exp k z
  have hval : (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y))) =
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) * y : ℝ) : ℂ)) *
        ((2 * (Real.pi : ℂ) * Complex.I) * (((-(k : ℝ)) : ℝ) : ℂ))) := by
    rw [eC_neg_mul_eq_exp]
    push_cast
    ring
  rw [hfun, hval]
  exact h3

/-- `eC` at a negative integer is one. -/
private lemma eC_neg_natCast (k : ℕ) : eC (-((k : ℝ))) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  rw [← h]
  unfold eC
  congr 1
  push_cast
  ring

/-- Scaling the integral of the phase returns the difference of two unit phases. -/
private lemma mul_integral_eC (k : ℕ) (α β : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * ∫ y in α..β, eC (-((k : ℝ) * y))
      = eC (-((k : ℝ) * α)) - eC (-((k : ℝ) * β)) := by
  have hcont := continuous_eC_neg_mul k
  have hFTC : ∫ y in α..β, (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      = eC (-((k : ℝ) * β)) - eC (-((k : ℝ) * α)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun z : ℝ => eC (-((k : ℝ) * z)))
      (f' := fun y : ℝ => -(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      (fun y _ => hasDerivAt_eC_neg_mul k y)
      ((continuous_const.mul hcont).intervalIntegrable _ _)
  have hsplit : ∫ y in α..β, (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * eC (-((k : ℝ) * y)))
      = (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))) * ∫ y in α..β, eC (-((k : ℝ) * y)) :=
    intervalIntegral.integral_const_mul _ _
  rw [hsplit] at hFTC
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * ∫ y in α..β, eC (-((k : ℝ) * y))
      = -((-(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))) * ∫ y in α..β, eC (-((k : ℝ) * y))) := by
    ring
  rw [h2, hFTC]
  ring

/-- Concluding step: if a unit-modulus difference is a scaled integral, the integral is small. -/
private lemma bound_of_scaled (k : ℕ) (hk : 1 ≤ k) (I X Y : ℂ)
    (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1)
    (h : (2 * (Real.pi : ℂ) * Complex.I * (k : ℝ)) * I = X - Y) :
    ‖I‖ ≤ 1 / (Real.pi * (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hAnorm := norm_two_pi_I_mul k
  have h1 : ‖(2 * (Real.pi : ℂ) * Complex.I * (k : ℝ))‖ * ‖I‖ = ‖X - Y‖ := by
    rw [← norm_mul, h]
  have h2 : ‖X - Y‖ ≤ 2 := by
    calc ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le X Y
      _ = 2 := by rw [hX, hY]; norm_num
  rw [hAnorm] at h1
  have h3 : Real.pi * (k : ℝ) * ‖I‖ ≤ 1 := by nlinarith [h1, h2, Real.pi_pos]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi * (k : ℝ))]
  linarith [h3]

/-- Integrability of an indicator times the phase. -/
private lemma intervalIntegrable_ind_mul_eC (k : ℕ) (p : ℝ → Prop) [DecidablePred p]
    (hp : MeasurableSet {y : ℝ | p y}) (A B : ℝ) :
    IntervalIntegrable (fun y : ℝ => (if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
      MeasureTheory.volume A B := by
  classical
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => (if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
      (MeasureTheory.volume.restrict (Set.uIoc A B)) :=
    ((Measurable.ite hp measurable_const measurable_const).mul
      (continuous_eC_neg_mul k).measurable).aestronglyMeasurable
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (2 : ℂ)) intervalIntegrable_const hmeas ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  have hA : ‖(if p y then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  have hB : ‖eC (-((k : ℝ) * y))‖ = 1 := norm_eC_one _
  have hle : ‖(if p y then (1 : ℂ) else 0) * eC (-((k : ℝ) * y))‖ ≤ 2 := by
    rw [norm_mul, hB, mul_one]
    linarith
  simpa using hle

/-- The Fourier coefficient of a periodic interval indicator. -/
private theorem fourier_coeff_interval_bound (k : ℕ) (hk : 1 ≤ k) (c₀ L : ℝ) :
    ‖∫ y in (0 : ℝ)..1, (if Int.fract (y - c₀) < L then (1 : ℂ) else 0) * eC (-((k : ℝ) * y))‖
      ≤ 1 / (Real.pi * (k : ℝ)) := by
  classical
  set r : ℝ := Int.fract (-c₀) with hr
  have hr0 : 0 ≤ r := Int.fract_nonneg _
  have hr1 : r < 1 := Int.fract_lt_one _
  set G : ℝ → ℂ := fun y => (if Int.fract (y + r) < L then (1 : ℂ) else 0) * eC (-((k : ℝ) * y))
    with hG
  have hfri : ∀ y : ℝ,
      (if Int.fract (y - c₀) < L then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)) = G y := by
    intro y
    have hm : y + r = (y - c₀) + ((-⌊-c₀⌋ : ℤ) : ℝ) := by
      rw [hr, Int.fract]
      push_cast
      ring
    rw [hG]
    simp only
    rw [hm, Int.fract_add_intCast]
  have hFG : (∫ y in (0 : ℝ)..1,
        (if Int.fract (y - c₀) < L then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
      = ∫ y in (0 : ℝ)..1, G y :=
    intervalIntegral.integral_congr (fun y _ => hfri y)
  rw [hFG]
  have hp : MeasurableSet {y : ℝ | Int.fract (y + r) < L} :=
    measurableSet_lt (measurable_fract.comp (measurable_id.add measurable_const)) measurable_const
  by_cases hL0 : L ≤ 0
  · -- degenerate case: the indicator vanishes
    have hzero : ∀ y : ℝ, G y = 0 := by
      intro y
      have hlt : ¬ (Int.fract (y + r) < L) :=
        not_lt.mpr (le_trans hL0 (Int.fract_nonneg _))
      rw [hG]
      simp only
      rw [if_neg hlt, zero_mul]
    have hcong : (∫ y in (0 : ℝ)..1, G y) = ∫ y in (0 : ℝ)..1, (0 : ℂ) :=
      intervalIntegral.integral_congr (fun y _ => hzero y)
    rw [hcong, intervalIntegral.integral_zero, norm_zero]
    exact div_nonneg zero_le_one (by positivity)
  · have hL0' : 0 < L := lt_of_not_ge hL0
    by_cases hL1 : 1 ≤ L
    · -- saturated case: the indicator is one
      have hone : ∀ y : ℝ, G y = eC (-((k : ℝ) * y)) := by
        intro y
        have hlt : Int.fract (y + r) < L := lt_of_lt_of_le (Int.fract_lt_one _) hL1
        rw [hG]
        simp only
        rw [if_pos hlt, one_mul]
      have hcong : (∫ y in (0 : ℝ)..1, G y) = ∫ y in (0 : ℝ)..1, eC (-((k : ℝ) * y)) :=
        intervalIntegral.integral_congr (fun y _ => hone y)
      rw [hcong]
      exact bound_of_scaled k hk _ _ _ (norm_eC_one _) (norm_eC_one _) (mul_integral_eC k 0 1)
    · -- genuine indicator: split at the two possible positions of the arc
      have h1r0 : (0 : ℝ) ≤ 1 - r := by linarith
      have h1r1 : 1 - r ≤ 1 := by linarith
      have hs1 : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) (1 - r) :=
        intervalIntegrable_ind_mul_eC k _ hp 0 (1 - r)
      have hs2 : IntervalIntegrable G MeasureTheory.volume (1 - r) 1 :=
        intervalIntegrable_ind_mul_eC k _ hp (1 - r) 1
      by_cases hrL : r ≤ L
      · -- the arc ends before the period boundary
        set D : ℝ := L - r with hD
        have hDnn : 0 ≤ D := by rw [hD]; linarith
        have hDle : D ≤ 1 - r := by rw [hD]; linarith
        have hA1 : ∫ y in (0 : ℝ)..(1 - r), G y = ∫ y in (0 : ℝ)..D, eC (-((k : ℝ) * y)) := by
          have step : (∫ y in (0 : ℝ)..(1 - r), G y)
              = ∫ y in (0 : ℝ)..(1 - r),
                  (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)) := by
            apply intervalIntegral.integral_congr_uIoo
            intro y hy
            rw [Set.uIoo_of_le h1r0] at hy
            obtain ⟨hy0, hy1⟩ := hy
            have hfract : Int.fract (y + r) = y + r := by
              rw [Int.fract_eq_self]
              constructor <;> linarith
            have hcond : (Int.fract (y + r) < L) ↔ (y < D) := by
              rw [hfract, hD]
              constructor <;> intro h <;> linarith
            rw [hG]
            simp only
            simp only [hcond]
          rw [step]
          have hi1 : IntervalIntegrable
              (fun y : ℝ => (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
              MeasureTheory.volume (0 : ℝ) D := intervalIntegrable_ind_mul_eC k _ measurableSet_Iio 0 D
          have hi2 : IntervalIntegrable
              (fun y : ℝ => (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
              MeasureTheory.volume D (1 - r) :=
            intervalIntegrable_ind_mul_eC k _ measurableSet_Iio D (1 - r)
          rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
          have hz : ∫ y in D..(1 - r), (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)) = 0 := by
            have hfalse : ∀ y ∈ Set.uIoo D (1 - r), ¬ (y < D) := by
              intro y hy
              rw [Set.uIoo_of_le hDle] at hy
              exact not_lt.mpr hy.1.le
            have hcong : (∫ y in D..(1 - r),
                  (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
                = ∫ y in D..(1 - r), (0 : ℂ) :=
              intervalIntegral.integral_congr_uIoo (fun y hy => by
                rw [if_neg (hfalse y hy), zero_mul])
            rw [hcong, intervalIntegral.integral_zero]
          rw [hz, add_zero]
          exact intervalIntegral.integral_congr_uIoo (fun y hy => by
            rw [Set.uIoo_of_le hDnn] at hy
            rw [if_pos hy.2, one_mul])
        have hA2 : ∫ y in (1 - r)..1, G y = ∫ y in (1 - r)..1, eC (-((k : ℝ) * y)) := by
          apply intervalIntegral.integral_congr_uIoo
          intro y hy
          rw [Set.uIoo_of_le h1r1] at hy
          obtain ⟨hy1, hy2⟩ := hy
          have hfract : Int.fract (y + r) = y + r - 1 := by
            have h2 : y + r = (y + r - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
            have h1 : Int.fract (y + r) = Int.fract (y + r - 1) := by
              conv_lhs => rw [h2]
              rw [Int.fract_add_intCast]
            rw [h1, Int.fract_eq_self]
            constructor <;> linarith
          have hcond : Int.fract (y + r) < L := by
            rw [hfract]
            linarith
          rw [hG]
          simp only
          rw [if_pos hcond, one_mul]
        rw [← intervalIntegral.integral_add_adjacent_intervals hs1 hs2, hA1, hA2]
        refine bound_of_scaled k hk _ (eC (-((k : ℝ) * (1 - r)))) (eC (-((k : ℝ) * D)))
          (norm_eC_one _) (norm_eC_one _) ?_
        rw [mul_add, mul_integral_eC k 0 D, mul_integral_eC k (1 - r) 1]
        have h0 : eC (-((k : ℝ) * 0)) = 1 := by
          rw [show -((k : ℝ) * 0) = 0 by ring]
          unfold eC
          simp
        have h1 : eC (-((k : ℝ) * 1)) = 1 := by
          rw [show -((k : ℝ) * 1) = -((k : ℝ)) by ring]
          exact eC_neg_natCast k
        rw [h0, h1]
        ring
      · -- the arc crosses the period boundary
        have hrL' : L < r := lt_of_not_ge hrL
        set D : ℝ := L + 1 - r with hD
        have hD1 : 1 - r ≤ D := by rw [hD]; linarith
        have hD2 : D ≤ 1 := by rw [hD]; linarith
        have hA1 : ∫ y in (0 : ℝ)..(1 - r), G y = 0 := by
          have hfalse : ∀ y ∈ Set.uIoo (0 : ℝ) (1 - r), ¬ (Int.fract (y + r) < L) := by
            intro y hy
            rw [Set.uIoo_of_le h1r0] at hy
            obtain ⟨hy0, hy1⟩ := hy
            have hfract : Int.fract (y + r) = y + r := by
              rw [Int.fract_eq_self]
              constructor <;> linarith
            rw [hfract]
            linarith
          have hcong : (∫ y in (0 : ℝ)..(1 - r), G y) = ∫ y in (0 : ℝ)..(1 - r), (0 : ℂ) :=
            intervalIntegral.integral_congr_uIoo (fun y hy => by
              rw [hG]
              simp only
              rw [if_neg (hfalse y hy), zero_mul])
          rw [hcong, intervalIntegral.integral_zero]
        have hA2 : ∫ y in (1 - r)..1, G y = ∫ y in (1 - r)..D, eC (-((k : ℝ) * y)) := by
          have step : (∫ y in (1 - r)..1, G y)
              = ∫ y in (1 - r)..1, (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)) := by
            apply intervalIntegral.integral_congr_uIoo
            intro y hy
            rw [Set.uIoo_of_le h1r1] at hy
            obtain ⟨hy1, hy2⟩ := hy
            have hfract : Int.fract (y + r) = y + r - 1 := by
              have h2 : y + r = (y + r - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
              have h1 : Int.fract (y + r) = Int.fract (y + r - 1) := by
                conv_lhs => rw [h2]
                rw [Int.fract_add_intCast]
              rw [h1, Int.fract_eq_self]
              constructor <;> linarith
            have hcond : (Int.fract (y + r) < L) ↔ (y < D) := by
              rw [hfract, hD]
              constructor <;> intro h <;> linarith
            rw [hG]
            simp only
            simp only [hcond]
          rw [step]
          have hi1 : IntervalIntegrable
              (fun y : ℝ => (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
              MeasureTheory.volume (1 - r) D :=
            intervalIntegrable_ind_mul_eC k _ measurableSet_Iio (1 - r) D
          have hi2 : IntervalIntegrable
              (fun y : ℝ => (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
              MeasureTheory.volume D 1 := intervalIntegrable_ind_mul_eC k _ measurableSet_Iio D 1
          rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
          have hz : ∫ y in D..1, (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)) = 0 := by
            have hfalse : ∀ y ∈ Set.uIoo D 1, ¬ (y < D) := by
              intro y hy
              rw [Set.uIoo_of_le hD2] at hy
              exact not_lt.mpr hy.1.le
            have hcong : (∫ y in D..1, (if y < D then (1 : ℂ) else 0) * eC (-((k : ℝ) * y)))
                = ∫ y in D..1, (0 : ℂ) :=
              intervalIntegral.integral_congr_uIoo (fun y hy => by
                rw [if_neg (hfalse y hy), zero_mul])
            rw [hcong, intervalIntegral.integral_zero]
          rw [hz, add_zero]
          exact intervalIntegral.integral_congr_uIoo (fun y hy => by
            rw [Set.uIoo_of_le hD1] at hy
            rw [if_pos hy.2, one_mul])
        rw [← intervalIntegral.integral_add_adjacent_intervals hs1 hs2, hA1, hA2, zero_add]
        exact bound_of_scaled k hk _ (eC (-((k : ℝ) * (1 - r)))) (eC (-((k : ℝ) * D)))
          (norm_eC_one _) (norm_eC_one _) (mul_integral_eC k (1 - r) D)

/-- LEAF. Analytic estimate, the Fejer convolution step: the squared exponential
sum of the cutoff is nonnegative and carries mass at least a fixed multiple of
one on the short arc of length twice the shrinking parameter, so the smoothed
periodic indicator of the enlarged interval dominates the half open interval
indicator at every point. -/
theorem leaf_fejer_convolution_majorant
    (a b : ℝ) (H : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 2 ≤ H)
    (s : ℝ) (hs : 0 < s) (hs2 : 2 * s = 1 / ((H : ℝ) + 1)) :
    ∀ x : ℝ,
      (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        12 * (∫ t in (0 : ℝ)..1,
          (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
            (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
          + 12 * (b - a + 2 * s)
          - 12 * (∫ y in (0 : ℝ)..1,
              (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) := by
  sorry

/-- LEAF. Finite Fourier expansion identity: every coefficient family that
agrees with the weighted Fourier coefficients of the enlarged periodic
indicator has a truncated cosine sum equal to the fixed constant times the
difference of the smoothed indicator and its mean. -/
theorem leaf_fejer_sum_representation
    (a b s : ℝ) (H : ℕ) (hH : 1 ≤ H) (x : ℝ) (F : ℕ → ℂ)
    (hF : ∀ h, F h =
      (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) •
        ∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
            eC (-(((h : ℝ) + 1) * y))) :
    (∑ h ∈ Finset.range H, (F h * eC (((h : ℝ) + 1) * x)).re) =
      12 * (∫ t in (0 : ℝ)..1,
        (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
          (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
      - 12 * (∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) := by
  sorry

/-- LEAF. Coefficient estimate: the k-th Fourier coefficient of a periodic half
open interval indicator has modulus at most one over pi k. -/
theorem leaf_fourier_coefficient_le (a b s : ℝ) (H : ℕ) :
    ∀ h ∈ Finset.range H,
      ‖∫ y in (0 : ℝ)..1,
          (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
            eC (-(((h : ℝ) + 1) * y))‖ ≤ 1 / (Real.pi * ((h : ℝ) + 1)) := by
  intro h _
  have hk : 1 ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le h)
  have hb := fourier_coeff_interval_bound (h + 1) hk (a - s) (b - a + 2 * s)
  simpa [Nat.cast_add, Nat.cast_one] using hb

/-- The target statement, assembled from the three leaves; the cutoff one case
is proved here, since a constant coefficient already dominates the indicator
at that cutoff. -/
theorem leaf_one_sided_majorant_split :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
        c₀ ≤ C * (b - a + 1 / ((H : ℝ) + 1)) ∧
        (∀ h ∈ Finset.range H, ‖c h‖ ≤ C) ∧
        ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re := by
  refine ⟨12, by norm_num, ?_⟩
  intro a b H ha hab hb hH
  rcases eq_or_lt_of_le hH with h1 | h2
  · obtain rfl : H = 1 := h1.symm
    refine ⟨1, fun _ => 0, ?_, ?_, ?_⟩
    · have hcast : ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
      rw [hcast]
      have hhalf : (1 : ℝ) / ((1 : ℝ) + 1) = 1 / 2 := by norm_num
      rw [hhalf]
      nlinarith
    · intro h hh
      simp
    · intro x
      simp only [zero_mul, Complex.zero_re]
      split_ifs <;> norm_num
  · have hH1 : 1 ≤ H := by omega
    have hH2 : 2 ≤ H := h2
    set s : ℝ := 1 / (2 * ((H : ℝ) + 1)) with hsdef
    have hs : 0 < s := by rw [hsdef]; positivity
    have hs2 : 2 * s = 1 / ((H : ℝ) + 1) := by rw [hsdef]; field_simp
    let D : ℕ → ℂ := fun h => ∫ y in (0 : ℝ)..1,
      (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
        eC (-(((h : ℝ) + 1) * y))
    let c : ℕ → ℂ := fun h => (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) • D h
    refine ⟨12 * (b - a + 2 * s), c, ?_, ?_, ?_⟩
    · rw [hs2]
    · intro h hh
      have hhH : h + 1 ≤ H := by
        have := Finset.mem_range.mp hh
        omega
      have hHpos : (0 : ℝ) < (H : ℝ) := by
        have : (0 : ℕ) < H := by omega
        exact_mod_cast this
      have hkpos : (0 : ℝ) < (h : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
        linarith
      have hw0 : (0 : ℝ) ≤ ((h : ℝ) + 1) / (H : ℝ) := by positivity
      have hw1 : ((h : ℝ) + 1) / (H : ℝ) ≤ 1 := by
        rw [div_le_one hHpos]
        exact_mod_cast hhH
      have hw : |1 - ((h : ℝ) + 1) / (H : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hD : ‖D h‖ ≤ 1 / (Real.pi * ((h : ℝ) + 1)) :=
        leaf_fourier_coefficient_le a b s H h hh
      have hnorm : ‖c h‖ = |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| * ‖D h‖ := by
        show ‖(2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) • D h‖ = _
        rw [norm_smul, Real.norm_eq_abs]
      have h24 : |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| ≤ 24 := by
        have hsplit : |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| =
            24 * |1 - ((h : ℝ) + 1) / (H : ℝ)| := by
          rw [show (2 : ℝ) * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ)) =
            24 * (1 - ((h : ℝ) + 1) / (H : ℝ)) from by ring, abs_mul]
          norm_num
        rw [hsplit]
        nlinarith [hw]
      calc ‖c h‖ = |2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))| * ‖D h‖ := hnorm
        _ ≤ 24 * (1 / (Real.pi * ((h : ℝ) + 1))) := by
            exact mul_le_mul h24 hD (norm_nonneg _) (by norm_num)
        _ ≤ 12 := by
            rw [mul_one_div, div_le_iff₀ (by positivity)]
            nlinarith [Real.pi_gt_three, hkpos]
    · intro x
      have hm := leaf_fejer_convolution_majorant a b H ha hab hb hH2 s hs hs2 x
      have hsum : (∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re) =
          12 * (∫ t in (0 : ℝ)..1,
            (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
              (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
          - 12 * (∫ y in (0 : ℝ)..1,
              (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0)) :=
        leaf_fejer_sum_representation a b s H hH1 x c (fun h => rfl)
      rw [hsum]
      linarith

end LeanLab.ExceptionalSet.Decomp523a
