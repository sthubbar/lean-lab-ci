import Mathlib
import LeanLab.PNTPort.StrongPNT.Bridge

/-!
Second split of `Decomp429eSplitTransfer.mangoldt_partial_summation_identity`,
burst-20261122, session S123. Ramare 2013 page 118 and JRT 2023 page 3 proof of
Lemma 9. The identity is assembled from a finite partial summation identity up to x,
integrability of (psi t - t)/t^2 on (1, infinity), and the constant identity
1 + gamma + integral over (1, infinity) of (psi t - t)/t^2 = 0.
The assembly step, splitting the integral at x and evaluating the integral of 1/t,
is proved here. AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2
open ArithmeticFunction MeasureTheory Set Filter Topology Asymptotics

/-- Ramare 2013 page 118, Abel partial summation of the Mangoldt sum with weight
1/n, written as psi x / x plus the integral over (1, x] of psi t / t^2. PROVED S123 by
Mathlib's Abel summation `sum_mul_eq_sub_sub_integral_mul`. -/
theorem mangoldt_abel_finite (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Chebyshev.psi x / x + ∫ t in Set.Ioc 1 x, Chebyshev.psi t / t ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := hx
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx1)
  have hA := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => (vonMangoldt n : ℝ))
    (f := fun t : ℝ => t⁻¹) (a := 1) (b := x) zero_le_one hx1
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      have : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) := by
        apply ContinuousOn.neg
        apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
        intro t ht; have : (1:ℝ) ≤ t := ht.1; exact pow_ne_zero 2 (lt_of_lt_of_le one_pos this).ne'
      refine (this.integrableOn_Icc).congr_fun (fun t _ => ?_) measurableSet_Icc
      simp [deriv_inv])
  have hL : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      ∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊, (fun t : ℝ => t⁻¹) (k : ℝ) * (vonMangoldt k : ℝ) := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hfl]
    simp [div_eq_inv_mul]
  rw [hL, hA, ← Chebyshev.psi_eq_sum_Icc]
  have h01 : (∑ k ∈ Finset.Icc 0 ⌊(1 : ℝ)⌋₊, (vonMangoldt k : ℝ)) = 0 := by
    simp [Finset.sum_Icc_succ_top]
  rw [h01]
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ)) =
      -∫ u in Set.Ioc 1 x, Chebyshev.psi u / u ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [deriv_inv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hI]
  simp [div_eq_inv_mul]

/-- Helper for `psi_error_integrableOn`, PROVED S132: exp of minus c root log t is at most
24 over c^4 log^2 t, from x^4/4! at most exp x. -/
theorem exp_neg_le_log_sq {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    Real.exp (-c * Real.sqrt (Real.log t)) ≤ 24 / c ^ 4 * (Real.log t ^ 2)⁻¹ := by
  have hl : 0 < Real.log t := Real.log_pos ht
  set y := c * Real.sqrt (Real.log t) with hy
  have hy0 : 0 < y := by positivity
  have h4 : y ^ 4 = c ^ 4 * Real.log t ^ 2 := by
    have hs : Real.sqrt (Real.log t) ^ 4 = Real.log t ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hl.le]
    rw [hy, mul_pow, hs]
  have he := Real.pow_div_factorial_le_exp (x := y) hy0.le 4
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at he
  rw [neg_mul, Real.exp_neg, ← hy]
  have hpos : 0 < y ^ 4 / 24 := by positivity
  calc (Real.exp y)⁻¹ ≤ (y ^ 4 / 24)⁻¹ := inv_anti₀ hpos he
    _ = 24 / c ^ 4 * (Real.log t ^ 2)⁻¹ := by rw [h4]; field_simp

/-- Helper for `psi_error_integrableOn`, PROVED S132: 1/(t log^2 t) is integrable on (3, infinity),
as the derivative of -1/log t. -/
theorem integrable_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Ioi 3) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t => -(Real.log t)⁻¹) (l := 0)
    (fun t ht => ?_) (fun t ht => ?_) ?_
  · have ht0 : (0:ℝ) < t := by linarith [ht.out]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.out])).ne'
    have := ((Real.hasDerivAt_log ht0.ne').inv hl).neg
    convert this using 1
    field_simp
  · have : (0:ℝ) < t := by linarith [ht.out]
    positivity
  · simpa using (Real.tendsto_log_atTop.inv_tendsto_atTop).neg

/-- Formerly LEAF: Ramare 2013 page 118, the prime number theorem with error term, used to make
the improper integral of (psi t - t)/t^2 over (1, infinity) absolutely convergent.
Class HARD. PROVED S132 from the lab strong PNT `LeanLab.PNTPort.psi_explicit_strong`. -/
theorem psi_error_integrableOn :
    IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioi 1) := by
  have hmeas : Measurable (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) :=
    ((Chebyshev.psi_mono.measurable).sub measurable_id).div (measurable_id.pow_const 2)
  have h13 : Ioi (1:ℝ) = Ioc 1 3 ∪ Ioi 3 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [h13]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := Chebyshev.psi 3 + 3)
      (by simp [Real.volume_Ioc]) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have h1 : 1 < t := ht.1
    have h3 : t ≤ 3 := ht.2
    have hp0 := Chebyshev.psi_nonneg t
    have hp3 := Chebyshev.psi_mono h3
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
    rw [div_le_iff₀ (by positivity)]
    have : |Chebyshev.psi t - t| ≤ Chebyshev.psi 3 + 3 := by
      rw [abs_le]; constructor <;> linarith
    have h0 : 0 ≤ Chebyshev.psi 3 + 3 := by linarith
    nlinarith
  · obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
    have hint := (integrable_inv_mul_log_sq).const_mul (max K 0 * (24 / c ^ 4))
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht3 : 3 < t := ht
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos (by linarith)
    have hb := hK t (by linarith)
    have hE := exp_neg_le_log_sq hc (by linarith : 1 < t)
    have hKm : |Chebyshev.psi t - t| ≤ max K 0 * t * Real.exp (-c * Real.sqrt (Real.log t)) :=
      hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le) (Real.exp_pos _).le)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2),
      div_le_iff₀ (by positivity)]
    calc |Chebyshev.psi t - t| ≤ max K 0 * t * Real.exp (-c * Real.sqrt (Real.log t)) := hKm
      _ ≤ max K 0 * t * (24 / c ^ 4 * (Real.log t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg (le_max_right _ _) ht0.le)
      _ = max K 0 * (24 / c ^ 4) * (t * Real.log t ^ 2)⁻¹ * t ^ 2 := by
        field_simp

/-- JRT 2023 page 3 proof of Lemma 9, the Mellin identity: for real s > 1,
the integral over (1, infinity) of (psi t - t) t^(-s-1) equals the Mangoldt Dirichlet
series at s divided by s, minus 1/(s-1). Abel summation of the Mangoldt series with weight
n^(-s), plus the integral of t^(-s) over (1, infinity). Class MEDIUM. PROVED S132 by
Mathlib's Abel summation `tendsto_sum_mul_atTop_nhds_one_sub_integral₀` and the Chebyshev
bound `Chebyshev.psi_le_const_mul_self`. -/
theorem mellin_identity (s : ℝ) (hs : 1 < s) :
    ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) * t ^ (-s - 1) =
      (∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) / s - 1 / (s - 1) := by
  set C : ℝ := Real.log 4 + 4 with hC
  have hC0 : 0 < C := by positivity
  set f : ℝ → ℝ := fun t => t ^ (-s) with hf
  have hderiv : ∀ t : ℝ, 0 < t → deriv f t = -s * t ^ (-s - 1) := fun t ht =>
    (Real.hasDerivAt_rpow_const (p := -s) (Or.inl ht.ne')).deriv
  have hpsi_sum : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ)) = Chebyshev.psi t :=
    fun t => (Chebyshev.psi_eq_sum_Icc t).symm
  have hpsi_nat : ∀ n : ℕ, (∑ k ∈ Finset.Icc 0 n, (vonMangoldt k : ℝ)) = Chebyshev.psi n := by
    intro n; rw [← hpsi_sum n, Nat.floor_natCast]
  -- t^(-s) integrable on (1, ∞)
  have hint_s : IntegrableOn (fun t : ℝ => t ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpsi_meas : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  have hrp_meas : Measurable (fun t : ℝ => t ^ (-s - 1)) := measurable_id.pow_const _
  have hint_psi : IntegrableOn (fun t : ℝ => Chebyshev.psi t * t ^ (-s - 1)) (Ioi 1) := by
    refine (hint_s.const_mul C).mono' (hpsi_meas.mul hrp_meas).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := by linarith [ht.out]
    have hp := Chebyshev.psi_le_const_mul_self ht0.le
    have hp0 := Chebyshev.psi_nonneg t
    have hr0 := Real.rpow_pos_of_pos ht0 (-s - 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 hr0.le)]
    have : t * t ^ (-s - 1) = t ^ (-s) := by
      rw [Real.rpow_sub_one ht0.ne']; field_simp
    calc Chebyshev.psi t * t ^ (-s - 1) ≤ (C * t) * t ^ (-s - 1) :=
          mul_le_mul_of_nonneg_right hp hr0.le
      _ = C * t ^ (-s) := by rw [mul_assoc, this]
  have hint_t : IntegrableOn (fun t : ℝ => t * t ^ (-s - 1)) (Ioi 1) := by
    refine hint_s.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0:ℝ) < t := by linarith [ht.out]
    rw [Real.rpow_sub_one ht0.ne']; field_simp
  -- split
  have hsplit : ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) * t ^ (-s - 1) =
      (∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-s - 1)) - ∫ t in Ioi (1 : ℝ), t ^ (-s) := by
    have e2 : ∫ t in Ioi (1 : ℝ), t ^ (-s) = ∫ t in Ioi (1 : ℝ), t * t ^ (-s - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0:ℝ) < t := by linarith [ht.out]
      rw [Real.rpow_sub_one ht0.ne']; field_simp
    rw [e2, ← integral_sub hint_psi hint_t]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [sub_mul]
  have hpow : ∫ t in Ioi (1 : ℝ), t ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
    have : -s + 1 ≠ 0 := by linarith
    have : s - 1 ≠ 0 := by linarith
    field_simp; ring
  -- Abel summation
  have hAbel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := f)
    (c := fun n : ℕ => (vonMangoldt n : ℝ)) (l := 0) (by simp)
    (fun t ht => (Real.hasDerivAt_rpow_const (p := -s)
      (Or.inl (by linarith [ht.out] : (t:ℝ) ≠ 0) |>.imp id id)).differentiableAt)
    (by
      have hco : ContinuousOn (fun t : ℝ => -s * t ^ (-s - 1)) (Ici 1) := by
        refine continuousOn_const.mul ?_
        exact fun t ht => (Real.continuousAt_rpow_const _ _
          (Or.inl (by linarith [ht.out]))).continuousWithinAt
      refine (hco.congr (fun t ht => hderiv t (by linarith [ht.out]))).locallyIntegrableOn
        measurableSet_Ici)
    (by
      have hlim : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (1 - s)) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (by linarith : 0 < s - 1)).comp
          tendsto_natCast_atTop_atTop
        simpa [neg_sub] using this.const_mul C
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
      · simp only [hpsi_nat, hf]
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Chebyshev.psi_nonneg _)
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (0:ℝ) < n := by exact_mod_cast hn
        simp only [hpsi_nat, hf]
        have hp := Chebyshev.psi_le_const_mul_self hn0.le
        calc (n:ℝ) ^ (-s) * Chebyshev.psi n ≤ (n:ℝ) ^ (-s) * (C * n) :=
              mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hn0.le _)
          _ = C * (n:ℝ) ^ (1 - s) := by
              rw [show (1 - s) = -s + 1 by ring, Real.rpow_add_one hn0.ne']; ring)
    (g := fun t : ℝ => t ^ (-s))
    (by
      refine IsBigO.of_bound (s * C) ?_
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht0
      rw [hderiv t ht0, hpsi_sum]
      have hp := Chebyshev.psi_le_const_mul_self ht0.le
      have hp0 := Chebyshev.psi_nonneg t
      have hr0 := Real.rpow_pos_of_pos ht0 (-s - 1)
      have : t * t ^ (-s - 1) = t ^ (-s) := by
        rw [Real.rpow_sub_one ht0.ne']; field_simp
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _),
        abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < s), abs_of_pos hr0,
        abs_of_nonneg hp0]
      calc s * t ^ (-s - 1) * Chebyshev.psi t ≤ s * t ^ (-s - 1) * (C * t) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = s * C * t ^ (-s) := by rw [← this]; ring)
    ⟨Ioi 1, Ioi_mem_atTop 1, hint_s⟩
  -- identify the integral
  have hI : ∫ t in Ioi (1 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ) =
      -s * ∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hderiv t (by linarith [ht.out]), hpsi_sum]; ring
  rw [hI, zero_sub, neg_mul, neg_neg] at hAbel
  -- HasSum
  have hnn : ∀ n : ℕ, 0 ≤ (vonMangoldt n : ℝ) * (n : ℝ) ^ (-s) := fun n =>
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hHas : HasSum (fun n : ℕ => (vonMangoldt n : ℝ) * (n : ℝ) ^ (-s))
      (s * ∫ t in Ioi (1 : ℝ), Chebyshev.psi t * t ^ (-s - 1)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hAbel.congr (fun n => ?_)
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by ext; simp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hf]; ring
  rw [hHas.tsum_eq, hsplit, hpow]
  have : s ≠ 0 := by linarith
  field_simp

/-- JRT 2023 page 3 proof of Lemma 9, the Laurent expansion
-zeta'/zeta of s = 1/(s-1) - gamma + O of s - 1 at s = 1, written for the Mangoldt Dirichlet
series along real s tending to 1 from the right. Needs zeta of s = 1/(s-1) + gamma + O of s - 1
with the derivative, Mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and
`tendsto_riemannZeta_sub_one_div`. PROVED S132 by the removable singularity theorem applied
to zeta of s minus 1/(s-1). -/
theorem mangoldt_series_laurent :
    Tendsto (fun s : ℝ => (∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) - 1 / (s - 1))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant)) := by
  set γ : ℝ := Real.eulerMascheroniConstant with hγ
  set H : ℂ → ℂ := Function.update (fun z : ℂ => riemannZeta z - (z - 1)⁻¹) 1 (γ : ℂ) with hH
  have hHc : ContinuousAt H 1 := by
    rw [hH, continuousAt_update_same]
    simpa [one_div] using tendsto_riemannZeta_sub_one_div
  have hHne : ∀ z : ℂ, z ≠ 1 → H z = riemannZeta z - (z - 1)⁻¹ := fun z hz => by
    rw [hH, Function.update_of_ne hz]
  have hHd : Differentiable ℂ H := by
    rw [← differentiableOn_univ, ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (Filter.univ_mem)]
    refine ⟨fun z hz => ?_, hHc⟩
    have hz1 : z ≠ 1 := hz.2
    have hd : DifferentiableAt ℂ (fun z : ℂ => riemannZeta z - (z - 1)⁻¹) z :=
      (differentiableAt_riemannZeta hz1).sub
        ((differentiableAt_id.sub_const 1).inv (sub_ne_zero.mpr hz1))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact hHne w hw
  have hH'c : Continuous (deriv H) := (hHd.contDiff (n := 1)).continuous_deriv le_rfl
  have hzeta : ∀ z : ℂ, z ≠ 1 → riemannZeta z = H z + (z - 1)⁻¹ := fun z hz => by
    rw [hHne z hz]; ring
  have hzeta' : ∀ z : ℂ, z ≠ 1 → deriv riemannZeta z = deriv H z - ((z - 1) ^ 2)⁻¹ := by
    intro z hz
    have hz0 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    have hd : HasDerivAt (fun w : ℂ => H w + (w - 1)⁻¹) (deriv H z + -1 / (z - 1) ^ 2) z :=
      (hHd z).hasDerivAt.add (((hasDerivAt_id z).sub_const 1).inv hz0)
    have he : riemannZeta =ᶠ[𝓝 z] fun w : ℂ => H w + (w - 1)⁻¹ := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact hzeta w hw
    rw [he.deriv_eq, hd.deriv]; ring
  set E : ℂ → ℂ := fun z => (-(z - 1) * deriv H z - H z) / (1 + (z - 1) * H z) with hE
  have hEc : ContinuousAt E 1 := by
    refine ContinuousAt.div ?_ ?_ (by simp)
    · exact ((continuousAt_id.sub continuousAt_const).neg.mul hH'c.continuousAt).sub hHc
    · exact continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hHc)
  have hE1 : E 1 = -(γ : ℂ) := by
    simp [hE, hH]
  have hlim : Tendsto (fun s : ℝ => (E (s : ℂ)).re) (𝓝[>] 1) (𝓝 (-γ)) := by
    have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 ((1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds Complex.continuous_ofReal.continuousAt.tendsto
    have h2 := (Complex.continuous_re.tendsto _).comp ((Complex.ofReal_one ▸ hEc).tendsto.comp h1)
    rw [Complex.ofReal_one, hE1] at h2
    rw [Complex.neg_re, Complex.ofReal_re] at h2
    exact h2
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1 : ℝ) < s := hs
  set z : ℂ := (s : ℂ) with hz
  have hzre : 1 < z.re := by simpa [hz] using hs1
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hzre; simp at hzre
  have hz0 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hζ0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hzre
  have hL : ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s) : ℝ) : ℂ) = LSeries (fun n => (vonMangoldt n : ℂ)) z := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr (fun n => ?_)
    rw [LSeries.term_def₀ (by simp)]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp [hz]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hzre] at hL
  have key : (((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) - 1 / (s - 1) : ℝ) : ℂ) = E z := by
    rw [Complex.ofReal_sub, hL, hzeta' z hz1]
    push_cast
    rw [← hz]
    have hden : 1 + (z - 1) * H z ≠ 0 := by
      have : 1 + (z - 1) * H z = (z - 1) * riemannZeta z := by
        rw [hzeta z hz1]; field_simp; ring
      rw [this]; exact mul_ne_zero hz0 hζ0
    have hζ : riemannZeta z = (1 + (z - 1) * H z) / (z - 1) := by
      rw [hzeta z hz1]; field_simp; ring
    rw [hζ, hE]
    field_simp
    ring
  rw [← key, Complex.ofReal_re]

/-- JRT 2023 page 3, dominated convergence: as s tends to 1 from the right, the Mellin
integral tends to the integral of (psi t - t)/t^2. PROVED S132 from `psi_error_integrableOn`. -/
theorem mellin_tendsto :
    Tendsto (fun s : ℝ => ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) * t ^ (-s - 1))
      (𝓝[>] 1) (𝓝 (∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2)) := by
  have hmeasψ : Measurable (fun t : ℝ => Chebyshev.psi t - t) :=
    (Chebyshev.psi_mono.measurable).sub measurable_id
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => ‖(Chebyshev.psi t - t) / t ^ 2‖) ?_ ?_ psi_error_integrableOn.norm ?_
  · refine Eventually.of_forall fun s => ?_
    exact (hmeasψ.mul (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := by linarith
    have hs1 : (1:ℝ) < s := hs
    have hr : t ^ (-s - 1) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have h2 : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht0.le]; norm_cast
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_pos (by positivity : (0:ℝ) < t ^ 2),
      div_eq_mul_inv, ← h2]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := by linarith [ht.out]
    have hc : Continuous (fun s : ℝ => -s - 1) := by continuity
    have hca : ContinuousAt (fun s : ℝ => (Chebyshev.psi t - t) * t ^ (-s - 1)) 1 :=
      continuousAt_const.mul ((Real.continuousAt_const_rpow ht0.ne').comp hc.continuousAt)
    have hv : (Chebyshev.psi t - t) * t ^ (-(1:ℝ) - 1) = (Chebyshev.psi t - t) / t ^ 2 := by
      rw [show (-(1:ℝ) - 1) = -2 by norm_num, Real.rpow_neg ht0.le, div_eq_mul_inv]; norm_cast
    rw [← hv]
    exact tendsto_nhdsWithin_of_tendsto_nhds hca.tendsto

/-- JRT 2023 page 3, the algebra turning the Laurent expansion into the limit -1 - gamma
of the right side of the Mellin identity. PROVED S132. -/
theorem algebra_tendsto
    (hB : Tendsto (fun s : ℝ => (∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) - 1 / (s - 1))
      (𝓝[>] 1) (𝓝 (-Real.eulerMascheroniConstant))) :
    Tendsto (fun s : ℝ => (∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) / s - 1 / (s - 1))
      (𝓝[>] 1) (𝓝 (-1 - Real.eulerMascheroniConstant)) := by
  have hs : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := (hB.sub tendsto_const_nhds (b := 1)).div hs one_ne_zero
  have h' : Tendsto (fun s : ℝ => ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s)) - 1 / (s - 1) - 1) / s)
      (𝓝[>] 1) (𝓝 (-1 - Real.eulerMascheroniConstant)) := by
    convert h using 2; ring
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (1:ℝ) < s := hs
  have : s - 1 ≠ 0 := by linarith
  have : s ≠ 0 := by linarith
  field_simp
  ring

/-- Formerly LEAF: JRT 2023 page 3 proof of Lemma 9, the constant identity
1 + gamma + integral over (1, infinity) of (psi t - t)/t^2 = 0. Class HARD. PROVED S132
from the Mellin identity, dominated convergence and the Laurent expansion above. -/
theorem psi_error_integral_const :
    ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 =
      -1 - Real.eulerMascheroniConstant := by
  have h2 := algebra_tendsto mangoldt_series_laurent
  have h3 : Tendsto (fun s : ℝ => ∫ t in Ioi (1 : ℝ), (Chebyshev.psi t - t) * t ^ (-s - 1))
      (𝓝[>] 1) (𝓝 (-1 - Real.eulerMascheroniConstant)) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (mellin_identity s hs).symm
  exact tendsto_nhds_unique mellin_tendsto h3

/-- Exact statement of `Decomp429eSplitTransfer.mangoldt_partial_summation_identity`.
Formerly CONDITIONAL ON the LEAFs above, all now PROVED S132, so this is unconditional. -/
theorem mangoldt_partial_summation_identity_of_leaves (x : ℝ) (hx : 100000 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n / (n : ℝ)) =
      Real.log x - Real.eulerMascheroniConstant + (Chebyshev.psi x - x) / x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hI := psi_error_integrableOn
  have hIoc : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioc 1 x) :=
    hI.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) (Set.Ioi x) :=
    hI.mono_set (Set.Ioi_subset_Ioi hx1)
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t - t) / t ^ 2 =
      (∫ t in Set.Ioc 1 x, (Chebyshev.psi t - t) / t ^ 2) +
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) / t ^ 2 := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx1]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    have : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
      continuousOn_inv₀.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1])
    exact (this.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hlog : ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
    rw [← intervalIntegral.integral_of_le hx1, integral_inv_of_pos one_pos hx0, div_one]
  have hpt : ∫ t in Set.Ioc 1 x, Chebyshev.psi t / t ^ 2 =
      ∫ t in Set.Ioc 1 x, ((Chebyshev.psi t - t) / t ^ 2 + t⁻¹) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : t ≠ 0 := by linarith [ht.1]
    field_simp
    ring
  have hadd : ∫ t in Set.Ioc 1 x, ((Chebyshev.psi t - t) / t ^ 2 + t⁻¹) =
      (∫ t in Set.Ioc 1 x, (Chebyshev.psi t - t) / t ^ 2) + ∫ t in Set.Ioc 1 x, t⁻¹ :=
    integral_add hIoc hinv
  rw [mangoldt_abel_finite x hx1, hpt, hadd, hlog]
  have hc := psi_error_integral_const
  rw [hsplit] at hc
  have hxx : (Chebyshev.psi x - x) / x = Chebyshev.psi x / x - 1 := by
    field_simp
  rw [hxx]
  linarith

end LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2

#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_partial_summation_identity_of_leaves
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_abel_finite
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.psi_error_integrableOn
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.psi_error_integral_const
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mellin_identity
#print axioms LeanLab.ChirreHagen2025.Decomp429eSplitTransferP2.mangoldt_series_laurent
