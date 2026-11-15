import Mathlib
import LeanLab.PNTPort.StrongPNT.EulerMaclaurin

/-!
Finite Euler summation for the real Stirling identity.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.RamareSaouter2003.Stirling518

open Real Complex Set MeasureTheory Filter
open scoped Topology

lemma fract_on_unit (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    Int.fract x = x - n := by
  have hf : ⌊x⌋ = (n : ℤ) := Int.floor_eq_iff.mpr ⟨hx.1.le, by exact_mod_cast hx.2⟩
  change x - (⌊x⌋ : ℝ) = _
  rw [hf]
  norm_cast

lemma bernoulli_weight_intervalIntegrable (k n : ℕ) (f : ℝ → ℂ) (hf : Continuous f) :
    IntervalIntegrable (fun x : ℝ => (bernoulliFun k (Int.fract x) : ℂ) * f x)
      volume (n : ℝ) (n + 1) := by
  have hc : Continuous (fun x : ℝ => (bernoulliFun k (x - n) : ℂ) * f x) :=
    (Complex.continuous_ofReal.comp
      ((continuous_bernoulliFun k).comp (continuous_id.sub continuous_const))).mul hf
  apply (hc.intervalIntegrable (n : ℝ) (n + 1)).congr_uIoo
  intro x hx
  rw [uIoo_of_lt (by linarith : (n : ℝ) < n + 1)] at hx
  dsimp only
  rw [fract_on_unit n hx]

lemma bernoulli_parts_unit (k n : ℕ) (hk : k ≠ 1) (f df : ℝ → ℂ)
    (_hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x) :
    (k : ℂ) * (∫ x : ℝ in (n : ℝ)..(n + 1),
      (bernoulliFun (k - 1) (Int.fract x) : ℂ) * f x) =
      (_root_.bernoulli k : ℂ) * (f (n + 1) - f n) -
        ∫ x : ℝ in (n : ℝ)..(n + 1),
          (bernoulliFun k (Int.fract x) : ℂ) * df x := by
  have hu : Continuous (fun x : ℝ => (bernoulliFun k (x - n) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_bernoulliFun k).comp (continuous_id.sub continuous_const))
  have hu' : Continuous (fun x : ℝ =>
      (k : ℂ) * (bernoulliFun (k - 1) (x - n) : ℂ)) := by fun_prop
  have hdu (x : ℝ) : HasDerivAt (fun x : ℝ => (bernoulliFun k (x - n) : ℂ))
      ((k : ℂ) * (bernoulliFun (k - 1) (x - n) : ℂ)) x := by
    convert (((hasDerivAt_bernoulliFun k (x - n)).comp x
      ((hasDerivAt_id x).sub_const (n : ℝ))).ofReal_comp) using 1 <;> simp
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hdu x) (fun x _ => hd x)
    (hu'.intervalIntegrable (n : ℝ) (n + 1))
    (hdf.intervalIntegrable (n : ℝ) (n + 1))
  have h0 : bernoulliFun k ((n : ℝ) - n) = (_root_.bernoulli k : ℝ) := by
    rw [sub_self, bernoulliFun_eval_zero]
  have h1 : bernoulliFun k ((n : ℝ) + 1 - n) = (_root_.bernoulli k : ℝ) := by
    rw [show (n : ℝ) + 1 - n = 1 by ring,
      bernoulliFun_endpoints_eq_of_ne_one hk, bernoulliFun_eval_zero]
  have he (j : ℕ) (g : ℝ → ℂ) :
      (∫ x : ℝ in (n : ℝ)..(n + 1), (bernoulliFun j (x - n) : ℂ) * g x) =
        ∫ x : ℝ in (n : ℝ)..(n + 1), (bernoulliFun j (Int.fract x) : ℂ) * g x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro x hx
    dsimp only
    rw [fract_on_unit n hx]
  simp only [h0, h1, Complex.ofReal_ratCast] at h
  simp_rw [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul, he (k - 1) f, he k df] at h
  linear_combination h

lemma bernoulli_parts (k N : ℕ) (hk : k ≠ 1) (f df : ℝ → ℂ)
    (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀ x, HasDerivAt f (df x) x) :
    (k : ℂ) * (∫ x : ℝ in (0 : ℝ)..N,
      (bernoulliFun (k - 1) (Int.fract x) : ℂ) * f x) =
      (_root_.bernoulli k : ℂ) * (f N - f 0) -
        ∫ x : ℝ in (0 : ℝ)..N,
          (bernoulliFun k (Int.fract x) : ℂ) * df x := by
  have h := Finset.sum_congr rfl (fun n (_ : n ∈ Finset.range N) =>
    bernoulli_parts_unit k n hk f df hf hdf hd)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at h
  have hglue (j : ℕ) (g : ℝ → ℂ) (hg : Continuous g) :
      (∑ n ∈ Finset.range N, ∫ x : ℝ in (n : ℝ)..(n + 1),
        (bernoulliFun j (Int.fract x) : ℂ) * g x) =
        ∫ x : ℝ in (0 : ℝ)..N, (bernoulliFun j (Int.fract x) : ℂ) * g x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ => (n : ℝ))
        (n := N) (fun n _ => by
          simpa only [Nat.cast_add, Nat.cast_one] using
            bernoulli_weight_intervalIntegrable j n g hg))
  rw [hglue (k - 1) f hf, hglue k df hdf] at h
  have htel : (∑ n ∈ Finset.range N, (f ((n : ℝ) + 1) - f n)) = f N - f 0 := by
    simpa only [← Finset.sum_neg_distrib, neg_sub, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero] using congrArg Neg.neg (Finset.sum_range_sub' (fun n : ℕ => f n) N)
  rw [← Finset.sum_sub_distrib, htel] at h
  exact h

lemma shift_ne_zero (s : ℂ) (hs : 0 < s.im) (x : ℝ) : s + x ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

lemma inv_shift_derivative (s : ℂ) (hs : 0 < s.im) (p : ℕ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => (1 : ℂ) / (s + u) ^ (p + 1))
      (-(p + 1 : ℂ) / (s + x) ^ (p + 2)) x := by
  have hlin : HasDerivAt (fun u : ℝ => s + u) (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add s
  have hn := shift_ne_zero s hs x
  convert ((hlin.pow (p + 1)).inv (pow_ne_zero _ hn)) using 1
  · ext u
    simp
  · simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one]
    simp only [pow_succ]
    field_simp

lemma inv_shift_continuous (s : ℂ) (hs : 0 < s.im) (p : ℕ) :
    Continuous (fun x : ℝ => (1 : ℂ) / (s + x) ^ p) :=
  continuous_const.div ((continuous_const.add Complex.continuous_ofReal).pow p)
    (fun x => pow_ne_zero p (shift_ne_zero s hs x))

lemma finite_bernoulli_remainder (s : ℂ) (hs : 0 < s.im) (N : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..N, (bernoulliFun 1 (Int.fract x) : ℂ) / (s + x)) =
      (1 / (s + N) - 1 / s) / 12 -
        (1 / (s + N) ^ 3 - 1 / s ^ 3) / 360 +
        (∫ x : ℝ in (0 : ℝ)..N,
          (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4) / 4 := by
  have hc (p : ℕ) (a : ℂ) :
      Continuous (fun x : ℝ => -a / (s + x) ^ p) := by
    exact continuous_const.div ((continuous_const.add Complex.continuous_ofReal).pow p)
      (fun x => pow_ne_zero p (shift_ne_zero s hs x))
  have h2 := bernoulli_parts 2 N (by decide)
    (fun x : ℝ => (1 : ℂ) / (s + x))
    (fun x : ℝ => -(1 : ℂ) / (s + x) ^ 2)
    (by simpa using inv_shift_continuous s hs 1) (hc 2 1)
    (fun x => by convert inv_shift_derivative s hs 0 x using 1 <;> norm_num)
  have h3 := bernoulli_parts 3 N (by decide)
    (fun x : ℝ => (1 : ℂ) / (s + x) ^ 2)
    (fun x : ℝ => -(2 : ℂ) / (s + x) ^ 3)
    (inv_shift_continuous s hs 2) (hc 3 2)
    (fun x => by convert inv_shift_derivative s hs 1 x using 1; norm_num)
  have h4 := bernoulli_parts 4 N (by decide)
    (fun x : ℝ => (1 : ℂ) / (s + x) ^ 3)
    (fun x : ℝ => -(3 : ℂ) / (s + x) ^ 4)
    (inv_shift_continuous s hs 3) (hc 4 3)
    (fun x => by convert inv_shift_derivative s hs 2 x using 1; norm_num)
  have hb2 : _root_.bernoulli 2 = (1 / 6 : ℚ) := by decide +kernel
  have hb3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
  have hb4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
  have he (j p : ℕ) (a : ℂ) :
      (∫ x : ℝ in (0 : ℝ)..N,
        (bernoulliFun j (Int.fract x) : ℂ) * (-a / (s + x) ^ p)) =
        -a * ∫ x : ℝ in (0 : ℝ)..N,
          (bernoulliFun j (Int.fract x) : ℂ) / (s + x) ^ p := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    ring
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, hb2, hb3, hb4,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, Rat.cast_neg,
    Complex.ofReal_zero, add_zero, one_mul, zero_mul] at h2 h3 h4
  rw [he 2 2 1] at h2
  rw [he 3 3 2] at h3
  rw [he 4 4 3] at h4
  simp_rw [mul_one_div] at h2 h3 h4
  linear_combination h2 / 2 + h3 / 6 + h4 / 12

lemma shift_log_derivative (s : ℂ) (hs : 0 < s.im) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (s + u)) ((s + x)⁻¹) x := by
  have hslit : s + (x : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hs.ne'))
  simpa only [mul_one, Function.comp_def] using
    ((Complex.hasDerivAt_log hslit).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).const_add s)).comp_ofReal

lemma shift_log_continuous (s : ℂ) (hs : 0 < s.im) :
    Continuous (fun x : ℝ => Complex.log (s + x)) :=
  continuous_iff_continuousAt.mpr (fun x => (shift_log_derivative s hs x).continuousAt)

lemma shift_log_primitive (s : ℂ) (hs : 0 < s.im) (x : ℝ) :
    HasDerivAt (fun u : ℝ =>
      (s + u) * Complex.log (s + u) - (s + u)) (Complex.log (s + x)) x := by
  have hlin : HasDerivAt (fun u : ℝ => s + u) (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add s
  convert (hlin.mul (shift_log_derivative s hs x)).sub hlin using 1
  simp [mul_inv_cancel₀ (shift_ne_zero s hs x)]

lemma finite_sum_log (s : ℂ) (hs : 0 < s.im) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), Complex.log (s + k)) =
      (s + N + 1 / 2) * Complex.log (s + N) - (s + N) -
        ((s - 1 / 2) * Complex.log s - s) +
        (1 / (s + N) - 1 / s) / 12 -
        (1 / (s + N) ^ 3 - 1 / s ^ 3) / 360 +
        (∫ x : ℝ in (0 : ℝ)..N,
          (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4) / 4 := by
  have hd : deriv (fun x : ℝ => Complex.log (s + x)) =
      (fun x : ℝ => (s + x)⁻¹) := funext (fun x => (shift_log_derivative s hs x).deriv)
  have hc : Continuous (fun x : ℝ => (s + x)⁻¹) := by
    simpa only [one_div, pow_one] using inv_shift_continuous s hs 1
  have h := sum_eq_integral_add_integral_deriv
    (f := fun x : ℝ => Complex.log (s + x)) (a := 0) (b := N)
    (by norm_num) (by positivity)
    (fun x _ => (shift_log_derivative s hs x).differentiableAt)
    (by rw [hd]; exact hc.continuousOn)
  rw [hd] at h
  have hB0 : B1 0 = -(1 / 2 : ℝ) := by norm_num [B1]
  have hBN : B1 (N : ℝ) = -(1 / 2 : ℝ) := by simp [B1]
  simp only [Nat.floor_zero, Nat.floor_natCast, Complex.ofReal_natCast,
    Complex.ofReal_zero, add_zero, hB0, hBN, RCLike.ofReal_eq_complex_ofReal] at h
  have hB :
      (∫ x : ℝ in (0 : ℝ)..N, (s + x)⁻¹ * (B1 x : ℂ)) =
        ∫ x : ℝ in (0 : ℝ)..N,
          (bernoulliFun 1 (Int.fract x) : ℂ) / (s + x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ N)] at hx
      exact hx.1
    have he : B1 x = bernoulliFun 1 (Int.fract x) := by
      rw [bernoulliFun_one]
      change x - (⌊x⌋₊ : ℝ) - 1 / 2 = x - (⌊x⌋ : ℝ) - 1 / 2
      rw [natCast_floor_eq_intCast_floor hx0]
    dsimp only
    rw [he]
    ring
  rw [hB, finite_bernoulli_remainder s hs N] at h
  have hi :
      (∫ x : ℝ in (0 : ℝ)..N, Complex.log (s + x)) =
        (s + N) * Complex.log (s + N) - (s + N) - (s * Complex.log s - s) := by
    simpa only [Complex.ofReal_natCast, Complex.ofReal_zero, add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => shift_log_primitive s hs x)
        ((shift_log_continuous s hs).intervalIntegrable 0 N)
  rw [hi] at h
  have he : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [he, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, add_zero]
  rw [h]
  push_cast
  ring

lemma log_factorial_limit :
    Tendsto (fun n : ℕ => Real.log (n.factorial : ℝ) -
      (((n : ℝ) + 1 / 2) * Real.log n - n)) atTop
      (𝓝 (Real.log (Real.sqrt (2 * π)))) := by
  have hl := (Real.continuousAt_log
    (by positivity : Real.sqrt π ≠ 0)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hc : Real.log (Real.sqrt π) + Real.log 2 / 2 =
      Real.log (Real.sqrt (2 * π)) := by
    rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [← hc]
  apply (hl.add_const (Real.log 2 / 2)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Function.comp_def]
  rw [Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num) hnpos.ne', Real.log_div hnpos.ne' (Real.exp_ne_zero _),
    Real.log_exp]
  ring

lemma logarithmic_endpoint_limit (s : ℂ) (hs : 0 < s.im) :
    Tendsto (fun n : ℕ => (s + n + 1 / 2) *
      (Complex.log (s + n) - (Real.log n : ℂ)) - s) atTop (𝓝 0) := by
  have hd : HasDerivAt (fun u : ℝ => Complex.log (1 + s * u)) s 0 := by
    have hlinear : HasDerivAt (fun u : ℂ => 1 + s * u) s 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).const_mul s).const_add 1)
    have hlog : HasDerivAt Complex.log (1 : ℂ) (1 + s * 0) := by
      simpa using Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)
    simpa using (hlog.comp (0 : ℂ) hlinear).comp_ofReal
  have hu0 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu0, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    change 0 < (n : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hscaled : Tendsto (fun n : ℕ =>
      (n : ℂ) * Complex.log (1 + s * (n : ℂ)⁻¹)) atTop (𝓝 s) := by
    simpa [Function.comp_def, Complex.real_smul] using hd.tendsto_slope_zero_right.comp hu
  have hsmall : Tendsto (fun n : ℕ =>
      Complex.log (1 + s * (n : ℂ)⁻¹)) atTop (𝓝 (0 : ℂ)) := by
    simpa [Function.comp_def] using hd.continuousAt.tendsto.comp hu0
  have hmain := (hscaled.add (hsmall.const_mul (s + 1 / 2))).sub_const s
  simp only [mul_zero, add_zero, sub_self] at hmain
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : s + (n : ℂ) = (n : ℂ) * (1 + s * (n : ℂ)⁻¹) := by
    field_simp; ring
  have hz : 1 + s * (n : ℂ)⁻¹ ≠ 0 := by
    intro h
    apply shift_ne_zero s hs (n : ℝ)
    simp only [Complex.ofReal_natCast, he, h, mul_zero]
  have hlog : Complex.log (s + n) =
      (Real.log n : ℂ) + Complex.log (1 + s * (n : ℂ)⁻¹) := by
    rw [he]
    exact_mod_cast Complex.log_ofReal_mul hnpos hz
  rw [hlog]
  ring

lemma inv_shift_limit (s : ℂ) (hs : 0 < s.im) :
    Tendsto (fun n : ℕ => (s + (n : ℂ))⁻¹) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have h := hi.div (hi.const_mul s |>.const_add 1) (by simp : (1 + s * 0 : ℂ) ≠ 0)
  simp only [mul_zero, add_zero, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsne : s + (n : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_natCast] using shift_ne_zero s hs (n : ℝ)
  have hz : 1 + s * (n : ℂ)⁻¹ ≠ 0 := by
    intro hz
    apply hsne
    have he : (n : ℂ) * (1 + s * (n : ℂ)⁻¹) = s + n := by field_simp; ring
    rw [← he, hz, mul_zero]
  dsimp only [Pi.div_apply]
  field_simp [hnne, hsne, hz]
  linear_combination mul_inv_cancel₀ hsne

lemma integrable_shifted_four (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => 1 / (x + y) ^ 4) (Ioi (0 : ℝ)) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / (x + y) ^ 3) / 3)
      (1 / (x + y) ^ 4) x := by
    intro x hx
    have hxy : 0 < x + y := by linarith [show 0 ≤ x from hx]
    have hn : (x + y) ^ 3 ≠ 0 := pow_ne_zero 3 hxy.ne'
    convert (((((hasDerivAt_id x).add_const y).pow 3).inv hn).neg.div_const 3) using 1
    · ext z; simp
    · simp only [Pi.pow_apply, id_eq]
      field_simp; ring
  have ht : Tendsto (fun x : ℝ => (x + y) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right _ y tendsto_id)
  have hlim : Tendsto (fun x : ℝ => -(1 / (x + y) ^ 3) / 3) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, neg_zero, zero_div, Pi.inv_apply] using
      ht.inv_tendsto_atTop.neg.div_const 3
  exact integrableOn_Ioi_deriv_of_nonneg' hd (by intros; positivity) hlim

lemma fourth_kernel_integrable (s : ℂ) (hre : 0 ≤ s.re) (him : 0 < s.im) :
    IntegrableOn (fun x : ℝ => (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4)
      (Ioi (0 : ℝ)) := by
  have hB : Continuous (fun x : ℝ => bernoulliFun 4 (Int.fract x)) :=
    (continuous_bernoulliFun 4).continuousOn.comp_fract''
      (bernoulliFun_endpoints_eq_of_ne_one (by decide)).symm
  have hc : Continuous (fun x : ℝ =>
      (bernoulliFun 4 (Int.fract x) : ℂ) / (s + x) ^ 4) :=
    (Complex.continuous_ofReal.comp hB).div
      ((continuous_const.add Complex.continuous_ofReal).pow 4)
      (fun x => pow_ne_zero 4 (shift_ne_zero s him x))
  have hbound (x : ℝ) : |bernoulliFun 4 (Int.fract x)| ≤ 1 := by
    have h3 : _root_.bernoulli 3 = (0 : ℚ) := by decide +kernel
    have h4 : _root_.bernoulli 4 = (-1 / 30 : ℚ) := by decide +kernel
    have he (r : ℝ) : bernoulliFun 4 r = (r * (1 - r)) ^ 2 - 1 / 30 := by
      norm_num [bernoulliFun, Polynomial.bernoulli, Finset.sum_range_succ,
        h3, h4, Nat.choose]
      ring
    rw [he, abs_le]
    have hr0 := Int.fract_nonneg x
    have hr1 := (Int.fract_lt_one x).le
    have hq0 : 0 ≤ Int.fract x * (1 - Int.fract x) :=
      mul_nonneg hr0 (by linarith)
    have hq1 : Int.fract x * (1 - Int.fract x) ≤ 1 / 4 := by
      nlinarith [sq_nonneg (Int.fract x - 1 / 2)]
    constructor
    · nlinarith [sq_nonneg (Int.fract x * (1 - Int.fract x))]
    · nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  apply ((integrable_shifted_four s.im him).const_mul 4).mono'
    hc.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  have hsq : ‖s + x‖ ^ 2 = (s.re + x) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hnpos : 0 < ‖s + x‖ := norm_pos_iff.mpr (shift_ne_zero s him x)
  have hquad : (x + s.im) ^ 2 ≤ 2 * ‖s + x‖ ^ 2 := by
    nlinarith [sq_nonneg (x - s.im), mul_nonneg hre hx0]
  have hfour : (x + s.im) ^ 4 ≤ 4 * ‖s + x‖ ^ 4 := by
    nlinarith [sq_nonneg (2 * ‖s + x‖ ^ 2 - (x + s.im) ^ 2)]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    |bernoulliFun 4 (Int.fract x)| / ‖s + x‖ ^ 4 ≤ 1 / ‖s + x‖ ^ 4 :=
      div_le_div_of_nonneg_right (hbound x) (by positivity)
    _ ≤ 4 * (1 / (x + s.im) ^ 4) := by
      rw [div_le_iff₀ (pow_pos hnpos 4)]
      have hxy : (x + s.im) ^ 4 ≠ 0 := by positivity
      field_simp
      nlinarith [hfour]

lemma arg_upper_half_plane (s : ℂ) (hre : 0 ≤ s.re) (him : 0 < s.im) :
    s.arg = π / 2 - Real.arctan (s.re / s.im) := by
  have hs : s ≠ 0 := by
    intro h
    simp [h] at him
  have hθ0 : 0 < s.arg := by
    by_contra h
    have he : s.arg = 0 := le_antisymm (not_lt.mp h)
      (Complex.arg_nonneg_iff.mpr him.le)
    have hi := (Complex.arg_eq_zero_iff.mp he).2
    linarith
  have hθ1 : s.arg ≤ π / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hre)
  have ht : Real.tan (π / 2 - s.arg) = s.re / s.im := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
      Complex.cos_arg hs, Complex.sin_arg,
      div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hs)]
  have ha := Real.arctan_tan
    (show -(π / 2) < π / 2 - s.arg by linarith [Real.pi_pos])
    (show π / 2 - s.arg < π / 2 by linarith)
  rw [ht] at ha
  linarith

end LeanLab.RamareSaouter2003.Stirling518

#print axioms LeanLab.RamareSaouter2003.Stirling518.fract_on_unit
#print axioms LeanLab.RamareSaouter2003.Stirling518.bernoulli_weight_intervalIntegrable
#print axioms LeanLab.RamareSaouter2003.Stirling518.bernoulli_parts_unit
#print axioms LeanLab.RamareSaouter2003.Stirling518.bernoulli_parts
#print axioms LeanLab.RamareSaouter2003.Stirling518.shift_ne_zero
#print axioms LeanLab.RamareSaouter2003.Stirling518.inv_shift_derivative
#print axioms LeanLab.RamareSaouter2003.Stirling518.inv_shift_continuous
#print axioms LeanLab.RamareSaouter2003.Stirling518.finite_bernoulli_remainder
#print axioms LeanLab.RamareSaouter2003.Stirling518.shift_log_derivative
#print axioms LeanLab.RamareSaouter2003.Stirling518.shift_log_continuous
#print axioms LeanLab.RamareSaouter2003.Stirling518.shift_log_primitive
#print axioms LeanLab.RamareSaouter2003.Stirling518.finite_sum_log
#print axioms LeanLab.RamareSaouter2003.Stirling518.log_factorial_limit
#print axioms LeanLab.RamareSaouter2003.Stirling518.logarithmic_endpoint_limit
#print axioms LeanLab.RamareSaouter2003.Stirling518.inv_shift_limit
#print axioms LeanLab.RamareSaouter2003.Stirling518.integrable_shifted_four
#print axioms LeanLab.RamareSaouter2003.Stirling518.fourth_kernel_integrable
#print axioms LeanLab.RamareSaouter2003.Stirling518.arg_upper_half_plane
