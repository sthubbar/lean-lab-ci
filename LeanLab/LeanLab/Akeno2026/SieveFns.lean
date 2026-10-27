/-
P0087 M. Akeno, arXiv 2606.29559 v1, "On the level of distribution of Goldbach primes and its
applications". Lemma 4.1 page 30, proof of Theorem 1.2 pages 31 to 32, Appendix 5.1 pages 35
to 36. AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6767.
Checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here proves it.

Contents.
* `cR`: the functions `c_r` of Appendix 5.1, `c₁ = 1_{s ≥ 1}`, `c_r(s) = ∫_{r ≤ u ≤ s} c_{r-1}(u-1)/(u-1)`;
  `cR_mono_nonneg`, `cR_delay`.
* `IsOmegaPair`: the linear sieve functions `ω±` of Lemma 4.1; `A± = u ω±(u)` and the delay
  identities `omega_delay`, `Ap_two`, `Am_zero`, `Ap_mono`, `Am_mono`.
* Elementary log bounds `two_mul_div_le_log`, `log_le_half_sub_inv`, the weighted step bound
  `wstep`, the delay step `dstep`, the slope bound `incr`, the grid steps `grid_step`,
  `grid_step_const`, `kgrid_step`, and the grid inductions `level_ind`, `level_ind_const`.
* Integer tables on the grid `1/80` for `A±`, produced by an uncertified Python script; every
  step is checked by `decide +kernel`, so the script is not trusted.
* `omega_minus_bounds`: `ω⁻(5.47725) ∈ [0.56118, 0.56121]`, the printed enclosure, PROVED for
  every pair satisfying `IsOmegaPair`.
-/
import Mathlib

namespace LeanLab.Akeno2026.SieveFns
open Real Set MeasureTheory intervalIntegral

/-! ### Elementary log bounds -/

/-- `log y ≤ (y - y⁻¹)/2` for `y ≥ 1`, from `z ≤ sinh z`. -/
theorem log_le_half_sub_inv {y : ℝ} (hy : 1 ≤ y) : log y ≤ (y - y⁻¹) / 2 := by
  have h0 : 0 < y := by linarith
  rw [← sinh_log h0]
  exact self_le_sinh_iff.mpr (log_nonneg hy)

/-- `2(y-1)/(y+1) ≤ log y` for `y > 1`, the first term of the series for `log (1 + a⁻¹)`. -/
theorem two_mul_div_le_log {y : ℝ} (hy : 1 < y) : 2 * (y - 1) / (y + 1) ≤ log y := by
  have ha : 0 < (y - 1)⁻¹ := inv_pos.mpr (by linarith)
  have hs := hasSum_log_one_add_inv ha
  have hterm : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * (y - 1)⁻¹ + 1)) ^ (2 * k + 1) :=
    fun k => by positivity
  have h1 := sum_le_hasSum (s := {0}) (fun k _ => hterm k) hs
  rw [inv_inv, show 1 + (y - 1) = y by ring] at h1
  simp only [Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_add, pow_one] at h1
  have hy1 : y - 1 ≠ 0 := by linarith
  have e : (2 : ℝ) * (1 / 1) * (1 / (2 * (y - 1)⁻¹ + 1)) = 2 * (y - 1) / (y + 1) := by
    field_simp; ring
  linarith [e ▸ h1]

/-- Grid form: `2/(2j+1) ≤ log (1 + 1/j) ≤ (2j+1)/(2j(j+1))`. -/
theorem log_grid_bounds {j : ℝ} (hj : 0 < j) :
    2 / (2 * j + 1) ≤ log ((j + 1) / j) ∧ log ((j + 1) / j) ≤ (2 * j + 1) / (2 * j * (j + 1)) := by
  have hy : 1 < (j + 1) / j := by rw [lt_div_iff₀ hj]; linarith
  refine ⟨?_, ?_⟩
  · have := two_mul_div_le_log hy
    have e : 2 * ((j + 1) / j - 1) / ((j + 1) / j + 1) = 2 / (2 * j + 1) := by
      field_simp; ring
    linarith
  · have := log_le_half_sub_inv hy.le
    have e : ((j + 1) / j - ((j + 1) / j)⁻¹) / 2 = (2 * j + 1) / (2 * j * (j + 1)) := by
      field_simp; ring
    linarith

/-! ### A weighted step bound -/

/-- If `lo + dlo (u-a) ≤ f u ≤ hi + dhi (u-a)` on `[a,b]` and `w ≥ 0` is continuous with
`∫ w = W` and `∫ (u-a) w = V`, then `lo W + dlo V ≤ ∫ f w ≤ hi W + dhi V`. -/
theorem wstep {f w : ℝ → ℝ} {a b lo hi dlo dhi W V : ℝ} (hab : a ≤ b)
    (hfi : IntervalIntegrable (fun u => f u * w u) volume a b)
    (hw0 : ∀ u ∈ Icc a b, 0 ≤ w u) (hwc : ContinuousOn w (Icc a b))
    (hW : ∫ u in a..b, w u = W) (hV : ∫ u in a..b, (u - a) * w u = V)
    (hlo : ∀ u ∈ Icc a b, lo + dlo * (u - a) ≤ f u)
    (hhi : ∀ u ∈ Icc a b, f u ≤ hi + dhi * (u - a)) :
    lo * W + dlo * V ≤ ∫ u in a..b, f u * w u ∧ ∫ u in a..b, f u * w u ≤ hi * W + dhi * V := by
  have hwc' : ContinuousOn w (uIcc a b) := by rwa [uIcc_of_le hab]
  have hwi : IntervalIntegrable w volume a b := hwc'.intervalIntegrable
  have hvi : IntervalIntegrable (fun u => (u - a) * w u) volume a b :=
    ((continuous_id.sub continuous_const).continuousOn.mul hwc').intervalIntegrable
  have key : ∀ c d : ℝ, ∫ u in a..b, (c + d * (u - a)) * w u = c * W + d * V := by
    intro c d
    have e : (fun u => (c + d * (u - a)) * w u) = fun u => c * w u + d * ((u - a) * w u) := by
      funext u; ring
    rw [e, integral_add (hwi.const_mul c) (hvi.const_mul d), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hW, hV]
  have gi : ∀ c d : ℝ, IntervalIntegrable (fun u => (c + d * (u - a)) * w u) volume a b := by
    intro c d
    have e : (fun u => (c + d * (u - a)) * w u) = fun u => c * w u + d * ((u - a) * w u) := by
      funext u; ring
    rw [e]; exact (hwi.const_mul c).add (hvi.const_mul d)
  constructor
  · rw [← key]
    exact integral_mono_on hab (gi lo dlo) hfi
      (fun u hu => mul_le_mul_of_nonneg_right (hlo u hu) (hw0 u hu))
  · rw [← key]
    exact integral_mono_on hab hfi (gi hi dhi)
      (fun u hu => mul_le_mul_of_nonneg_right (hhi u hu) (hw0 u hu))

/-- `∫_a^b (u-1)⁻¹ = log ((b-1)/(a-1))` and `∫_a^b (u-a)(u-1)⁻¹ = (b-a) - (a-1) log(...)`. -/
theorem weight_shift {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ u in a..b, (u - 1)⁻¹ = log ((b - 1) / (a - 1))) ∧
    ∫ u in a..b, (u - a) * (u - 1)⁻¹ = (b - a) - (a - 1) * log ((b - 1) / (a - 1)) := by
  have h1 : ∫ u in a..b, (u - 1)⁻¹ = log ((b - 1) / (a - 1)) := by
    rw [intervalIntegral.integral_comp_sub_right (fun x => x⁻¹),
      integral_inv_of_pos (by linarith) (by linarith)]
  refine ⟨h1, ?_⟩
  have hc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; rw [uIcc_of_le hab] at hu; linarith [hu.1]
  have e : ∫ u in a..b, (u - a) * (u - 1)⁻¹ = ∫ u in a..b, (1 - (a - 1) * (u - 1)⁻¹) := by
    apply integral_congr
    intro u hu; rw [uIcc_of_le hab] at hu
    have : u - 1 ≠ 0 := by linarith [hu.1]
    field_simp; ring
  rw [e, integral_sub intervalIntegrable_const (hc.intervalIntegrable.const_mul _),
    intervalIntegral.integral_const_mul, h1]
  simp

/-- `∫_a^b (t-u)⁻¹ = log ((t-a)/(t-b))` and `∫_a^b (u-a)(t-u)⁻¹ = -(b-a) + (t-a) log(...)`. -/
theorem weight_refl {a b t : ℝ} (hab : a ≤ b) (hbt : b < t) :
    (∫ u in a..b, (t - u)⁻¹ = log ((t - a) / (t - b))) ∧
    ∫ u in a..b, (u - a) * (t - u)⁻¹ = -(b - a) + (t - a) * log ((t - a) / (t - b)) := by
  have h1 : ∫ u in a..b, (t - u)⁻¹ = log ((t - a) / (t - b)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x⁻¹),
      integral_inv_of_pos (by linarith) (by linarith)]
  refine ⟨h1, ?_⟩
  have hc : ContinuousOn (fun u : ℝ => (t - u)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; rw [uIcc_of_le hab] at hu; linarith [hu.2]
  have e : ∫ u in a..b, (u - a) * (t - u)⁻¹ = ∫ u in a..b, ((t - a) * (t - u)⁻¹ - 1) := by
    apply integral_congr
    intro u hu; rw [uIcc_of_le hab] at hu
    have : t - u ≠ 0 := by linarith [hu.2]
    field_simp; ring
  rw [e, integral_sub (hc.intervalIntegrable.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, h1]
  simp; ring


/-! ### One step of a delay integral -/

/-- One step for `g b - g a = ∫_a^b f(u-1)/(u-1) du` with `f` monotone and two-sided linear
bounds for `f(u-1)` on `[a,b]`. -/
theorem dstep {g f : ℝ → ℝ} {a b lo hi dlo dhi ΛL ΛU : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hdel : g b - g a = ∫ u in a..b, f (u - 1) / (u - 1))
    (hfm : MonotoneOn f (Icc (a - 1) (b - 1)))
    (hlo : ∀ u ∈ Icc a b, lo + dlo * (u - a) ≤ f (u - 1))
    (hhi : ∀ u ∈ Icc a b, f (u - 1) ≤ hi + dhi * (u - a))
    (hΛL : ΛL ≤ log ((b - 1) / (a - 1))) (hΛU : log ((b - 1) / (a - 1)) ≤ ΛU)
    (h0 : 0 ≤ lo) (h1 : 0 ≤ hi) (h2 : 0 ≤ dlo) (h3 : 0 ≤ dhi) :
    g a + lo * ΛL + dlo * ((b - a) - (a - 1) * ΛU) ≤ g b ∧
      g b ≤ g a + hi * ΛU + dhi * ((b - a) - (a - 1) * ΛL) := by
  obtain ⟨hW, hV⟩ := weight_shift ha hab
  have hfm' : MonotoneOn (fun u => f (u - 1)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hfm ⟨by linarith [hx.1], by linarith [hx.2]⟩ ⟨by linarith [hy.1], by linarith [hy.2]⟩
      (by linarith)
  have hc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; rw [uIcc_of_le hab] at hu; linarith [hu.1]
  have hfi : IntervalIntegrable (fun u => f (u - 1) * (u - 1)⁻¹) volume a b :=
    (hfm'.intervalIntegrable (μ := volume)).mul_continuousOn hc
  have hw0 : ∀ u ∈ Icc a b, 0 ≤ (u - 1)⁻¹ := fun u hu => inv_nonneg.mpr (by linarith [hu.1])
  have hwc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (Icc a b) := by rwa [← uIcc_of_le hab]
  obtain ⟨s1, s2⟩ := wstep (f := fun u => f (u - 1)) hab hfi hw0 hwc hW hV hlo hhi
  simp only [← div_eq_mul_inv] at s1 s2
  rw [← hdel] at s1 s2
  have hpos : 0 ≤ a - 1 := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hΛL h0, mul_le_mul_of_nonneg_left hΛU h2,
      mul_nonneg h2 hpos]
  · nlinarith [mul_le_mul_of_nonneg_left hΛU h1, mul_le_mul_of_nonneg_left hΛL h3,
      mul_nonneg h3 hpos]

/-- Increment bounds: if `f x - f p = ∫_p^x e(v-1)/(v-1) dv` on `[p,q]`, `p > 1`, and `e` is
monotone and nonnegative on `[p-1,q-1]`, then the slope of `f` lies in
`[e(p-1)/(q-1), e(q-1)/(p-1)]`. -/
theorem incr {f e : ℝ → ℝ} {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    (hdel : ∀ x ∈ Icc p q, f x - f p = ∫ v in p..x, e (v - 1) / (v - 1))
    (hem : MonotoneOn e (Icc (p - 1) (q - 1))) (he0 : 0 ≤ e (p - 1)) (x : ℝ) (hx : x ∈ Icc p q) :
    (x - p) * (e (p - 1) / (q - 1)) ≤ f x - f p ∧ f x - f p ≤ (x - p) * (e (q - 1) / (p - 1)) := by
  have hpx := hx.1
  have hxq := hx.2
  have hem' : MonotoneOn (fun v => e (v - 1)) (uIcc p x) := by
    rw [uIcc_of_le hpx]
    intro y hy z hz hyz
    exact hem ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨by linarith [hz.1], by linarith [hz.2]⟩
      (by linarith)
  have hc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (uIcc p x) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; rw [uIcc_of_le hpx] at hu; linarith [hu.1]
  have hfi : IntervalIntegrable (fun v => e (v - 1) / (v - 1)) volume p x := by
    simp only [div_eq_mul_inv]; exact hem'.intervalIntegrable.mul_continuousOn hc
  have hev : ∀ v ∈ Icc p x, e (p - 1) ≤ e (v - 1) ∧ e (v - 1) ≤ e (q - 1) := by
    intro v hv
    exact ⟨hem ⟨le_rfl, by linarith⟩ ⟨by linarith [hv.1], by linarith [hv.2]⟩ (by linarith [hv.1]),
      hem ⟨by linarith [hv.1], by linarith [hv.2]⟩ ⟨by linarith, le_rfl⟩ (by linarith [hv.2])⟩
  rw [hdel x hx]
  constructor
  · have := integral_mono_on hpx intervalIntegrable_const hfi (fun v hv => by
      obtain ⟨h1, _⟩ := hev v hv
      have hv1 : 0 < v - 1 := by linarith [hv.1]
      calc e (p - 1) / (q - 1) ≤ e (p - 1) / (v - 1) :=
            div_le_div_of_nonneg_left he0 hv1 (by linarith [hv.2])
        _ ≤ e (v - 1) / (v - 1) := div_le_div_of_nonneg_right h1 hv1.le)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have := integral_mono_on hpx hfi intervalIntegrable_const (fun v hv => by
      obtain ⟨h1, h2⟩ := hev v hv
      have hv1 : 0 < v - 1 := by linarith [hv.1]
      calc e (v - 1) / (v - 1) ≤ e (q - 1) / (v - 1) := div_le_div_of_nonneg_right h2 hv1.le
        _ ≤ e (q - 1) / (p - 1) :=
            div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith [hv.1]))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith


/-! ### Grid steps with scaled integer tables -/

set_option maxHeartbeats 1000000 in
/-- One grid step `K/M → (K+1)/M` of `g b - g a = ∫ f(u-1)/(u-1)`, with `K = J + M`,
`J = I + M`, `f` itself a delay integral of `e`, and tables scaled by `D`. -/
theorem grid_step {g f e : ℝ → ℝ} {M I J K D Lg Ug Lf Uf Le Ue Lg' Ug' : ℝ}
    (hM : 0 < M) (hI : 0 < I) (hJ : J = I + M) (hK : K = J + M) (hD : 0 < D)
    (hdel : g ((K + 1) / M) - g (K / M) = ∫ u in K / M..(K + 1) / M, f (u - 1) / (u - 1))
    (hdelf : ∀ x ∈ Icc (J / M) ((J + 1) / M), f x - f (J / M) = ∫ v in J / M..x, e (v - 1) / (v - 1))
    (hfm : MonotoneOn f (Icc (J / M) ((J + 1) / M)))
    (hem : MonotoneOn e (Icc (I / M) ((I + 1) / M)))
    (hg : Lg / D ≤ g (K / M) ∧ g (K / M) ≤ Ug / D)
    (hf : Lf / D ≤ f (J / M) ∧ f (J / M) ≤ Uf / D)
    (he : Le / D ≤ e (I / M) ∧ e ((I + 1) / M) ≤ Ue / D)
    (hLf : 0 ≤ Lf) (hLe : 0 ≤ Le)
    (cL : Lg' * ((2 * J + 1) * (2 * (I + 1) * (J + 1))) ≤
      Lg * ((2 * J + 1) * (2 * (I + 1) * (J + 1))) + 2 * Lf * (2 * (I + 1) * (J + 1)) +
        Le * (2 * J + 1))
    (cU : Ug * (2 * J * (J + 1) * (I * (2 * J + 1))) + Uf * (2 * J + 1) * (I * (2 * J + 1)) +
        Ue * (2 * J * (J + 1)) ≤ Ug' * (2 * J * (J + 1) * (I * (2 * J + 1)))) :
    Lg' / D ≤ g ((K + 1) / M) ∧ g ((K + 1) / M) ≤ Ug' / D := by
  have hJ0 : 0 < J := by linarith
  have hJM : M < J := by linarith
  have ha : 1 < K / M := by rw [lt_div_iff₀ hM]; linarith
  have hab : K / M ≤ (K + 1) / M := div_le_div_of_nonneg_right (by linarith) hM.le
  have ea : K / M - 1 = J / M := by rw [hK]; field_simp; ring
  have eb : (K + 1) / M - 1 = (J + 1) / M := by rw [hK]; field_simp; ring
  have ep : J / M - 1 = I / M := by rw [hJ]; field_simp; ring
  have eq : (J + 1) / M - 1 = (I + 1) / M := by rw [hJ]; field_simp; ring
  have hp : 1 < J / M := by rw [lt_div_iff₀ hM]; linarith
  have hpq : J / M ≤ (J + 1) / M := div_le_div_of_nonneg_right (by linarith) hM.le
  have he0 : 0 ≤ e (I / M) := le_trans (div_nonneg hLe hD.le) he.1
  have hinc := incr hp hpq hdelf (by rw [ep, eq]; exact hem) (by rw [ep]; exact he0)
  rw [ep, eq] at hinc
  have hratio : ((K + 1) / M - 1) / (K / M - 1) = (J + 1) / J := by
    rw [ea, eb]; field_simp
  obtain ⟨hΛL, hΛU⟩ := log_grid_bounds hJ0
  rw [← hratio] at hΛL hΛU
  have hlo : ∀ u ∈ Icc (K / M) ((K + 1) / M),
      Lf / D + (Le / D / ((I + 1) / M)) * (u - K / M) ≤ f (u - 1) := by
    intro u hu
    have hx : u - 1 ∈ Icc (J / M) ((J + 1) / M) := by
      constructor <;> linarith [hu.1, hu.2]
    have h1 := (hinc (u - 1) hx).1
    have hua : u - 1 - J / M = u - K / M := by linarith
    rw [hua] at h1
    have hd : Le / D / ((I + 1) / M) ≤ e (I / M) / ((I + 1) / M) :=
      div_le_div_of_nonneg_right he.1 (by positivity)
    have hu0 : 0 ≤ u - K / M := by linarith [hu.1]
    linarith [mul_le_mul_of_nonneg_left hd hu0, hf.1]
  have hhi : ∀ u ∈ Icc (K / M) ((K + 1) / M),
      f (u - 1) ≤ Uf / D + (Ue / D / (I / M)) * (u - K / M) := by
    intro u hu
    have hx : u - 1 ∈ Icc (J / M) ((J + 1) / M) := by
      constructor <;> linarith [hu.1, hu.2]
    have h1 := (hinc (u - 1) hx).2
    have hua : u - 1 - J / M = u - K / M := by linarith
    rw [hua] at h1
    have hd : e ((I + 1) / M) / (I / M) ≤ Ue / D / (I / M) :=
      div_le_div_of_nonneg_right he.2 (by positivity)
    have hu0 : 0 ≤ u - K / M := by linarith [hu.1]
    linarith [mul_le_mul_of_nonneg_left hd hu0, hf.2]
  have hfm' : MonotoneOn f (Icc (K / M - 1) ((K + 1) / M - 1)) := by rw [ea, eb]; exact hfm
  have hUf : 0 ≤ Uf / D := le_trans (div_nonneg hLf hD.le) (hf.1.trans hf.2)
  have hUe : 0 ≤ Ue / D := le_trans he0 (le_trans (hem ⟨le_rfl, by
      rw [div_le_div_iff_of_pos_right hM]; linarith⟩ ⟨by rw [div_le_div_iff_of_pos_right hM]; linarith,
      le_rfl⟩ (by rw [div_le_div_iff_of_pos_right hM]; linarith)) he.2)
  obtain ⟨s1, s2⟩ := dstep ha hab hdel hfm' hlo hhi hΛL hΛU (div_nonneg hLf hD.le) hUf
    (by positivity) (by positivity)
  rw [ea] at s1 s2
  constructor
  · have e1 : Lg / D + Lf / D * (2 / (2 * J + 1)) + Le / D / ((I + 1) / M) *
        ((K + 1) / M - K / M - J / M * ((2 * J + 1) / (2 * J * (J + 1)))) =
        (Lg * ((2 * J + 1) * (2 * (I + 1) * (J + 1))) + 2 * Lf * (2 * (I + 1) * (J + 1)) +
          Le * (2 * J + 1)) / (D * ((2 * J + 1) * (2 * (I + 1) * (J + 1)))) := by
      rw [hK]; field_simp; ring
    have e2 : Lg' / D = Lg' * ((2 * J + 1) * (2 * (I + 1) * (J + 1))) /
        (D * ((2 * J + 1) * (2 * (I + 1) * (J + 1)))) := by field_simp
    have : Lg' / D ≤ Lg / D + Lf / D * (2 / (2 * J + 1)) + Le / D / ((I + 1) / M) *
        ((K + 1) / M - K / M - J / M * ((2 * J + 1) / (2 * J * (J + 1)))) := by
      rw [e1, e2]; exact div_le_div_of_nonneg_right cL (by positivity)
    linarith [hg.1]
  · have e1 : Ug / D + Uf / D * ((2 * J + 1) / (2 * J * (J + 1))) + Ue / D / (I / M) *
        ((K + 1) / M - K / M - J / M * (2 / (2 * J + 1))) =
        (Ug * (2 * J * (J + 1) * (I * (2 * J + 1))) + Uf * (2 * J + 1) * (I * (2 * J + 1)) +
          Ue * (2 * J * (J + 1))) / (D * (2 * J * (J + 1) * (I * (2 * J + 1)))) := by
      rw [hK]; field_simp; ring
    have e2 : Ug' / D = Ug' * (2 * J * (J + 1) * (I * (2 * J + 1))) /
        (D * (2 * J * (J + 1) * (I * (2 * J + 1)))) := by field_simp
    have : Ug / D + Uf / D * ((2 * J + 1) / (2 * J * (J + 1))) + Ue / D / (I / M) *
        ((K + 1) / M - K / M - J / M * (2 / (2 * J + 1))) ≤ Ug' / D := by
      rw [e1, e2]; exact div_le_div_of_nonneg_right cU (by positivity)
    linarith [hg.2]

/-- The grid step when `f` is constant on `[J/M, (J+1)/M]`. -/
theorem grid_step_const {g f : ℝ → ℝ} {M J K D Lg Ug Lf Uf Lg' Ug' : ℝ}
    (hM : 0 < M) (hJ0 : 0 < J) (hK : K = J + M) (hD : 0 < D)
    (hdel : g ((K + 1) / M) - g (K / M) = ∫ u in K / M..(K + 1) / M, f (u - 1) / (u - 1))
    (hconst : ∀ x ∈ Icc (J / M) ((J + 1) / M), f x = f (J / M))
    (hg : Lg / D ≤ g (K / M) ∧ g (K / M) ≤ Ug / D)
    (hf : Lf / D ≤ f (J / M) ∧ f (J / M) ≤ Uf / D) (hLf : 0 ≤ Lf)
    (cL : Lg' * (2 * J + 1) ≤ Lg * (2 * J + 1) + 2 * Lf)
    (cU : Ug * (2 * J * (J + 1)) + Uf * (2 * J + 1) ≤ Ug' * (2 * J * (J + 1))) :
    Lg' / D ≤ g ((K + 1) / M) ∧ g ((K + 1) / M) ≤ Ug' / D := by
  have ha : 1 < K / M := by rw [lt_div_iff₀ hM]; linarith
  have hab : K / M ≤ (K + 1) / M := div_le_div_of_nonneg_right (by linarith) hM.le
  have ea : K / M - 1 = J / M := by rw [hK]; field_simp; ring
  have eb : (K + 1) / M - 1 = (J + 1) / M := by rw [hK]; field_simp; ring
  have hratio : ((K + 1) / M - 1) / (K / M - 1) = (J + 1) / J := by
    rw [ea, eb]; field_simp
  obtain ⟨hΛL, hΛU⟩ := log_grid_bounds hJ0
  rw [← hratio] at hΛL hΛU
  have hc : ∀ u ∈ Icc (K / M) ((K + 1) / M), f (u - 1) = f (J / M) := by
    intro u hu; exact hconst _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hfm' : MonotoneOn f (Icc (K / M - 1) ((K + 1) / M - 1)) := by
    intro x hx y hy _
    rw [ea, eb] at hx hy
    rw [hconst x hx, hconst y hy]
  have hUf : 0 ≤ Uf / D := le_trans (div_nonneg hLf hD.le) (hf.1.trans hf.2)
  obtain ⟨s1, s2⟩ := dstep (dlo := 0) (dhi := 0) ha hab hdel hfm'
    (fun u hu => by rw [hc u hu]; linarith [hf.1]) (fun u hu => by rw [hc u hu]; linarith [hf.2])
    hΛL hΛU (div_nonneg hLf hD.le) hUf le_rfl le_rfl
  constructor
  · have : Lg' / D ≤ Lg / D + Lf / D * (2 / (2 * J + 1)) := by
      have e1 : Lg / D + Lf / D * (2 / (2 * J + 1)) = (Lg * (2 * J + 1) + 2 * Lf) / (D * (2 * J + 1)) := by
        field_simp
      have e2 : Lg' / D = Lg' * (2 * J + 1) / (D * (2 * J + 1)) := by field_simp
      rw [e1, e2]; exact div_le_div_of_nonneg_right cL (by positivity)
    linarith [hg.1]
  · have : Ug / D + Uf / D * ((2 * J + 1) / (2 * J * (J + 1))) ≤ Ug' / D := by
      have e1 : Ug / D + Uf / D * ((2 * J + 1) / (2 * J * (J + 1))) =
          (Ug * (2 * J * (J + 1)) + Uf * (2 * J + 1)) / (D * (2 * J * (J + 1))) := by
        field_simp
      have e2 : Ug' / D = Ug' * (2 * J * (J + 1)) / (D * (2 * J * (J + 1))) := by field_simp
      rw [e1, e2]; exact div_le_div_of_nonneg_right cU (by positivity)
    linarith [hg.2]


/-! ### The functions `c_r` of Appendix 5.1 -/

/-- `c₁(s) = 1_{s ≥ 1}`, `c_r(s) = ∫_{r ≤ u ≤ s} c_{r-1}(u-1)/(u-1) du` for `r ≥ 2`, page 36.
`cR 0` is an unused filler. -/
noncomputable def cR : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => if 1 ≤ s then 1 else 0
  | r + 2, s => ∫ u in Icc ((r : ℝ) + 2) s, cR (r + 1) (u - 1) / (u - 1)

/-- For monotone `f` and `1 < a`, `u ↦ f(u-1)/(u-1)` is integrable on `[a,b]`. -/
theorem integrableOn_shift {f : ℝ → ℝ} (hf : Monotone f) {a b : ℝ} (ha : 1 < a) :
    IntegrableOn (fun u => f (u - 1) / (u - 1)) (Icc a b) := by
  have h1 : IntegrableOn (fun u => f (u - 1)) (Icc a b) :=
    (show Monotone (fun u => f (u - 1)) from fun x y hxy => hf (by linarith)).monotoneOn
      _ |>.integrableOn_isCompact isCompact_Icc
  have h2 : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; linarith [hu.1]
  simpa [div_eq_mul_inv] using h1.mul_continuousOn h2 isCompact_Icc

theorem cR_mono_nonneg : ∀ r, Monotone (cR r) ∧ ∀ s, 0 ≤ cR r s
  | 0 => ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  | 1 => by
    refine ⟨fun x y hxy => ?_, fun s => ?_⟩
    · simp only [cR]
      by_cases h1 : 1 ≤ x
      · simp only [h1, le_trans h1 hxy, ite_true, le_refl]
      · simp only [h1, ite_false]; split_ifs <;> norm_num
    · simp only [cR]; split_ifs <;> norm_num
  | r + 2 => by
    obtain ⟨hm, h0⟩ := cR_mono_nonneg (r + 1)
    have hr : (1 : ℝ) < (r : ℝ) + 2 := by have := r.cast_nonneg (α := ℝ); linarith
    have hint : ∀ s, 0 ≤ ∫ u in Icc ((r : ℝ) + 2) s, cR (r + 1) (u - 1) / (u - 1) := by
      intro s
      apply setIntegral_nonneg measurableSet_Icc
      intro u hu
      exact div_nonneg (h0 _) (by linarith [hu.1])
    refine ⟨fun x y hxy => ?_, fun s => hint s⟩
    simp only [cR]
    apply setIntegral_mono_set (integrableOn_shift hm hr)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact div_nonneg (h0 _) (by linarith [hu.1])
    · exact Filter.Eventually.of_forall (fun u hu => ⟨hu.1, le_trans hu.2 hxy⟩)


theorem cR_delay (r : ℕ) {a b : ℝ} (ha : (r : ℝ) + 2 ≤ a) (hab : a ≤ b) :
    cR (r + 2) b - cR (r + 2) a = ∫ u in a..b, cR (r + 1) (u - 1) / (u - 1) := by
  have hr : (1 : ℝ) < (r : ℝ) + 2 := by have := r.cast_nonneg (α := ℝ); linarith
  have hI : ∀ c, (r : ℝ) + 2 ≤ c → IntervalIntegrable (fun u => cR (r + 1) (u - 1) / (u - 1))
      volume ((r : ℝ) + 2) c := by
    intro c hc
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hc]
    exact integrableOn_shift (cR_mono_nonneg (r + 1)).1 hr
  simp only [cR]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ha.trans hab), ← intervalIntegral.integral_of_le ha,
    intervalIntegral.integral_interval_sub_left (hI b (ha.trans hab)) (hI a ha)]

theorem cR_base (r : ℕ) : cR (r + 2) ((r : ℝ) + 2) = 0 := by
  simp [cR, Icc_self]

theorem cR_one {x : ℝ} (hx : 1 ≤ x) : cR 1 x = 1 := by simp [cR, hx]

/-! ### The linear sieve functions `ω±` and `A± = u ω±(u)`, Lemma 4.1 and page 35 -/

/-- Lemma 4.1: `ω⁺(s) = 2/s`, `ω⁻(s) = 0` for `0 < s ≤ 2`, `(s ω±(s))' = ω∓(s-1)` for `s > 2`,
with values in `ℝ≥0`; continuity on `(0,∞)` is the standard implicit condition. -/
def IsOmegaPair (ωp ωm : ℝ → ℝ) : Prop :=
  (∀ s, 0 < s → 0 ≤ ωp s ∧ 0 ≤ ωm s) ∧
  (∀ s, 0 < s → s ≤ 2 → ωp s = 2 / s ∧ ωm s = 0) ∧
  ContinuousOn ωp (Ioi 0) ∧ ContinuousOn ωm (Ioi 0) ∧
  ∀ s, 2 < s → HasDerivAt (fun x => x * ωp x) (ωm (s - 1)) s ∧
    HasDerivAt (fun x => x * ωm x) (ωp (s - 1)) s

section Omega
variable {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm)
include hω

/-- The FTC form of the delay equations: for `2 ≤ a ≤ b`,
`A^∓(b) - A^∓(a) = ∫_a^b A^±(u-1)/(u-1) du`, where `A^± (x) = x ω^±(x)`. -/
theorem omega_delay {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b * ωm b - a * ωm a = ∫ u in a..b, ((u - 1) * ωp (u - 1)) / (u - 1)) ∧
    (b * ωp b - a * ωp a = ∫ u in a..b, ((u - 1) * ωm (u - 1)) / (u - 1)) := by
  obtain ⟨_, _, hcp, hcm, hd⟩ := hω
  have hsub : MapsTo (fun u : ℝ => u - 1) (Icc a b) (Ioi 0) := fun u hu => by
    simp only [mem_Ioi]; linarith [hu.1]
  have hsub' : Icc a b ⊆ Ioi 0 := fun u hu => by simp only [mem_Ioi]; linarith [hu.1]
  have hc1 : ContinuousOn (fun u => ωp (u - 1)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcp.comp (by fun_prop) hsub
  have hc2 : ContinuousOn (fun u => ωm (u - 1)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcm.comp (by fun_prop) hsub
  have ecg : ∀ (w : ℝ → ℝ), ∫ u in a..b, ((u - 1) * w (u - 1)) / (u - 1) = ∫ u in a..b, w (u - 1) := by
    intro w
    apply integral_congr
    intro u hu; rw [uIcc_of_le hab] at hu
    have : u - 1 ≠ 0 := by linarith [hu.1]
    field_simp
  rw [ecg, ecg]
  constructor
  · rw [integral_eq_sub_of_hasDerivAt_of_le hab ((continuous_id.continuousOn).mul (hcm.mono hsub'))
      (fun x hx => (hd x (by linarith [hx.1])).2) hc1.intervalIntegrable]
    rfl
  · rw [integral_eq_sub_of_hasDerivAt_of_le hab ((continuous_id.continuousOn).mul (hcp.mono hsub'))
      (fun x hx => (hd x (by linarith [hx.1])).1) hc2.intervalIntegrable]
    rfl

theorem Am_zero {x : ℝ} (hx : x ≤ 2) (hx0 : 0 ≤ x) : x * ωm x = 0 := by
  rcases hx0.eq_or_lt with h | h
  · rw [← h]; ring
  · rw [(hω.2.1 x h hx).2, mul_zero]

theorem Ap_two {x : ℝ} (hx : x ≤ 3) (hx0 : 0 < x) : x * ωp x = 2 := by
  rcases le_or_gt x 2 with h | h
  · rw [(hω.2.1 x hx0 h).1]; field_simp
  · have h2 : (2 : ℝ) * ωp 2 = 2 := by rw [(hω.2.1 2 (by norm_num) le_rfl).1]; norm_num
    have := (omega_delay hω le_rfl h.le).2
    rw [h2] at this
    have hz : ∫ u in (2 : ℝ)..x, ((u - 1) * ωm (u - 1)) / (u - 1) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply integral_congr
      intro u hu; rw [uIcc_of_le h.le] at hu
      simp only
      rw [Am_zero hω (x := u - 1) (by linarith [hu.2]) (by linarith [hu.1])]; simp
    linarith

theorem Ap_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ x * ωp x := mul_nonneg hx.le (hω.1 x hx).1
theorem Am_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ x * ωm x := mul_nonneg hx.le (hω.1 x hx).2

theorem Am_mono : MonotoneOn (fun x => x * ωm x) (Ici 1) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  rcases le_or_gt y 2 with h | h
  · simp only; rw [Am_zero hω (hxy.trans h) (by linarith), Am_zero hω h (by linarith)]
  rcases le_or_gt x 2 with h' | h'
  · simp only; rw [Am_zero hω h' (by linarith)]; exact Am_nonneg hω (by linarith)
  have := (omega_delay hω h'.le hxy).1
  have hnn : 0 ≤ ∫ u in x..y, ((u - 1) * ωp (u - 1)) / (u - 1) := by
    apply intervalIntegral.integral_nonneg hxy
    intro u hu
    exact div_nonneg (Ap_nonneg hω (by linarith [hu.1])) (by linarith [hu.1])
  simp only; linarith

theorem Ap_mono : MonotoneOn (fun x => x * ωp x) (Ici 1) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  have hstep : ∀ p q : ℝ, 2 ≤ p → p ≤ q → p * ωp p ≤ q * ωp q := by
    intro p q hp hpq
    have := (omega_delay hω hp hpq).2
    have hnn : 0 ≤ ∫ u in p..q, ((u - 1) * ωm (u - 1)) / (u - 1) := by
      apply intervalIntegral.integral_nonneg hpq
      intro u hu
      exact div_nonneg (Am_nonneg hω (by linarith [hu.1])) (by linarith [hu.1])
    linarith
  rcases le_or_gt x 2 with h | h
  · simp only; rw [Ap_two hω (by linarith) (by linarith)]
    rcases le_or_gt y 2 with h' | h'
    · rw [Ap_two hω (by linarith) (by linarith)]
    · have := hstep 2 y le_rfl h'.le
      rw [Ap_two hω (by norm_num) (by norm_num)] at this; exact this
  · exact hstep x y h.le hxy

end Omega


/-! ### Integer certificates and induction along the grid -/

/-- Lower step check, cross-multiplied. -/
def chkL (Lg' Lg Lf Le j i : ℕ) : Bool :=
  decide (Lg' * ((2 * j + 1) * (2 * (i + 1) * (j + 1))) ≤
    Lg * ((2 * j + 1) * (2 * (i + 1) * (j + 1))) + 2 * Lf * (2 * (i + 1) * (j + 1)) + Le * (2 * j + 1))

/-- Upper step check, cross-multiplied. -/
def chkU (Ug' Ug Uf Ue j i : ℕ) : Bool :=
  decide (Ug * (2 * j * (j + 1) * (i * (2 * j + 1))) + Uf * (2 * j + 1) * (i * (2 * j + 1)) +
    Ue * (2 * j * (j + 1)) ≤ Ug' * (2 * j * (j + 1) * (i * (2 * j + 1))))

/-- Checks when `f` is constant on the step. -/
def chkLc (Lg' Lg Lf j : ℕ) : Bool := decide (Lg' * (2 * j + 1) ≤ Lg * (2 * j + 1) + 2 * Lf)
def chkUc (Ug' Ug Uf j : ℕ) : Bool :=
  decide (Ug * (2 * j * (j + 1)) + Uf * (2 * j + 1) ≤ Ug' * (2 * j * (j + 1)))

/-- Table bounds for `g` at the grid point `k/M`, scale `D`. -/
def TB (g : ℝ → ℝ) (M D : ℕ) (L U : ℕ → ℕ) (k : ℕ) : Prop :=
  (L k : ℝ) / D ≤ g ((k : ℝ) / M) ∧ g ((k : ℝ) / M) ≤ (U k : ℝ) / D

set_option maxHeartbeats 1000000 in
/-- Induction along the grid for one function `g` whose delay integrand `f` is itself a delay
integral of `e`. -/
theorem level_ind {g f e : ℝ → ℝ} {M D N k0 : ℕ} {Lg Ug Lf Uf Le Ue : ℕ → ℕ}
    (hM : 0 < M) (hD : 0 < D) (hk0 : 2 * M < k0)
    (hdel : ∀ a b : ℝ, (k0 : ℝ) / M ≤ a → a ≤ b → g b - g a = ∫ u in a..b, f (u - 1) / (u - 1))
    (hdelf : ∀ p x : ℝ, ((k0 - M : ℕ) : ℝ) / M ≤ p → p ≤ x →
      f x - f p = ∫ v in p..x, e (v - 1) / (v - 1))
    (hfm : MonotoneOn f (Ici (((k0 - M : ℕ) : ℝ) / M)))
    (hem : MonotoneOn e (Ici (((k0 - 2 * M : ℕ) : ℝ) / M)))
    (hfb : ∀ j, k0 - M ≤ j → j + M < N → TB f M D Lf Uf j)
    (heb : ∀ i, k0 - 2 * M ≤ i → i + 2 * M < N → TB e M D Le Ue i ∧ TB e M D Le Ue (i + 1))
    (hbase : TB g M D Lg Ug k0)
    (hchk : ∀ k, k0 ≤ k → k < N →
      chkL (Lg (k + 1)) (Lg k) (Lf (k - M)) (Le (k - 2 * M)) (k - M) (k - 2 * M) = true ∧
      chkU (Ug (k + 1)) (Ug k) (Uf (k - M)) (Ue (k - 2 * M + 1)) (k - M) (k - 2 * M) = true) :
    ∀ k, k0 ≤ k → k ≤ N → TB g M D Lg Ug k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact hbase
  | succ k hk ih =>
    intro hkN
    have hgk := ih (by omega)
    obtain ⟨c1, c2⟩ := hchk k hk (by omega)
    obtain ⟨j, hj⟩ : ∃ j, j = k - M := ⟨_, rfl⟩
    obtain ⟨i, hi⟩ : ∃ i, i = k - 2 * M := ⟨_, rfl⟩
    have hkj : k = j + M := by omega
    have hji : j = i + M := by omega
    have hi1 : k - 2 * M + 1 = i + 1 := by omega
    rw [hi1] at c2
    rw [← hj, ← hi] at c1 c2
    simp only [chkL, chkU, decide_eq_true_eq] at c1 c2
    have hfj := hfb j (by omega) (by omega)
    obtain ⟨hei, hei1⟩ := heb i (by omega) (by omega)
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hIr : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have hJr : (j : ℝ) = i + M := by exact_mod_cast hji
    have hKr : (k : ℝ) = j + M := by exact_mod_cast hkj
    have hk0r : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    have hj0 : ((k0 - M : ℕ) : ℝ) ≤ j := by exact_mod_cast (show k0 - M ≤ j by omega)
    have hi0 : ((k0 - 2 * M : ℕ) : ℝ) ≤ i := by exact_mod_cast (show k0 - 2 * M ≤ i by omega)
    have hdiv : ∀ x y : ℝ, x ≤ y → x / M ≤ y / M := fun x y h => div_le_div_of_nonneg_right h hMr.le
    have key := grid_step (g := g) (f := f) (e := e) (M := M) (I := i) (J := j) (K := k) (D := D)
      (Lg := Lg k) (Ug := Ug k) (Lf := Lf j) (Uf := Uf j) (Le := Le i) (Ue := Ue (i + 1))
      (Lg' := Lg (k + 1)) (Ug' := Ug (k + 1)) hMr hIr hJr hKr hDr
      (hdel _ _ (hdiv _ _ hk0r) (hdiv _ _ (by linarith)))
      (fun x hx => hdelf _ _ (hdiv _ _ hj0) hx.1)
      (hfm.mono (fun x hx => le_trans (hdiv _ _ hj0) hx.1))
      (hem.mono (fun x hx => le_trans (hdiv _ _ hi0) hx.1))
      hgk hfj ⟨hei.1, by have := hei1.2; push_cast at this; exact this⟩
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast c1) (by exact_mod_cast c2)
    unfold TB; push_cast; exact key

/-- Induction along the grid when the delay integrand `f` is constant on `[(k0-M)/M, ∞)`. -/
theorem level_ind_const {g f : ℝ → ℝ} {M D N k0 : ℕ} {Lg Ug Lf Uf : ℕ → ℕ}
    (hM : 0 < M) (hD : 0 < D) (hk0 : M < k0)
    (hdel : ∀ a b : ℝ, (k0 : ℝ) / M ≤ a → a ≤ b → g b - g a = ∫ u in a..b, f (u - 1) / (u - 1))
    (hfc : ∀ x y : ℝ, x ∈ Icc (((k0 - M : ℕ) : ℝ) / M) (((N - M : ℕ) : ℝ) / M) →
      y ∈ Icc (((k0 - M : ℕ) : ℝ) / M) (((N - M : ℕ) : ℝ) / M) → f x = f y)
    (hfb : ∀ j, k0 - M ≤ j → j + M < N → TB f M D Lf Uf j)
    (hbase : TB g M D Lg Ug k0)
    (hchk : ∀ k, k0 ≤ k → k < N →
      chkLc (Lg (k + 1)) (Lg k) (Lf (k - M)) (k - M) = true ∧
      chkUc (Ug (k + 1)) (Ug k) (Uf (k - M)) (k - M) = true) :
    ∀ k, k0 ≤ k → k ≤ N → TB g M D Lg Ug k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact hbase
  | succ k hk ih =>
    intro hkN
    have hgk := ih (by omega)
    obtain ⟨c1, c2⟩ := hchk k hk (by omega)
    obtain ⟨j, hj⟩ : ∃ j, j = k - M := ⟨_, rfl⟩
    have hkj : k = j + M := by omega
    rw [← hj] at c1 c2
    simp only [chkLc, chkUc, decide_eq_true_eq] at c1 c2
    have hfj := hfb j (by omega) (by omega)
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hJ0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hKr : (k : ℝ) = j + M := by exact_mod_cast hkj
    have hk0r : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    have hj0 : ((k0 - M : ℕ) : ℝ) ≤ j := by exact_mod_cast (show k0 - M ≤ j by omega)
    have hjN : (j : ℝ) + 1 ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast (show j + 1 ≤ N - M by omega)
    have hdiv : ∀ x y : ℝ, x ≤ y → x / M ≤ y / M := fun x y h => div_le_div_of_nonneg_right h hMr.le
    have key := grid_step_const (g := g) (f := f) (M := M) (J := j) (K := k) (D := D)
      (Lg := Lg k) (Ug := Ug k) (Lf := Lf j) (Uf := Uf j)
      (Lg' := Lg (k + 1)) (Ug' := Ug (k + 1)) hMr hJ0 hKr hDr
      (hdel _ _ (hdiv _ _ hk0r) (hdiv _ _ (by linarith)))
      (fun x hx => hfc _ _ ⟨le_trans (hdiv _ _ hj0) hx.1, le_trans hx.2 (hdiv _ _ hjN)⟩
        ⟨hdiv _ _ hj0, le_trans (hdiv _ _ (by linarith)) (hdiv _ _ hjN)⟩)
      hgk hfj (Nat.cast_nonneg _) (by exact_mod_cast c1) (by exact_mod_cast c2)
    unfold TB; push_cast; exact key

/-! ### Certificate tables, grid `1/80`, scale `10⁹`, generated by an uncertified script and
checked below by `decide` -/

/-- Lower table for `A⁻` at `k/80`, scaled by `10⁹`. -/
def tAmL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 24844720, 49384597, 73627021, 97579116, 121247755, 144639567, 167760954,
   190618096, 213216966, 235563334, 257662781, 279520704, 301142325, 322532699, 343696720,
   364639128, 385364516, 405877336, 426181904, 446282406, 466182903, 485887336, 505399531,
   524723202, 543861957, 562819302, 581598644, 600203295, 618636474, 636901314, 655000861,
   672938080, 690715857, 708337002, 725804250, 743120267, 760287648, 777308924, 794186561,
   810922962, 827520472, 843981377, 860307907, 876502238, 892566495, 908502749, 924313025,
   939999299, 955563501, 971007516, 986333186, 1001542311, 1016636650, 1031617923, 1046487811,
   1061247958, 1075899972, 1090445426, 1104885859, 1119222776, 1133457651, 1147591926,
   1161627013, 1175564295, 1189405125, 1203150829, 1216802706, 1230362028, 1243830041,
   1257207967, 1270497003, 1283698323, 1296813077, 1309842392, 1322787375, 1335649111,
   1348428663, 1361127075, 1373745371, 1386284555, 1398745614, 1411129514, 1423437206,
   1435669621, 1447827675, 1459912267, 1471924279, 1483864577, 1495734013, 1507533423,
   1519263628, 1530925435, 1542519637, 1554047014, 1565508332, 1576904343, 1588235787,
   1599503392, 1610707873, 1621849934, 1632930266, 1643949549, 1654908453, 1665807635,
   1676647743, 1687429414, 1698153274, 1708819940, 1719430019, 1729984108, 1740482795,
   1750926659, 1761316269, 1771652186, 1781934962, 1792165141, 1802343258, 1812469840,
   1822545406, 1832570468, 1842545530, 1852471088, 1862347631, 1872175640, 1881955591,
   1891687951, 1901373181, 1911011735, 1920604061, 1930150600, 1939651787, 1949108051,
   1958519815, 1967887496, 1977211505, 1986492247, 1995730122, 2004925524, 2014078842,
   2023190459, 2032260753, 2041290098, 2050278862, 2059227407, 2068136092, 2077005271,
   2085835293, 2094626501, 2103379236, 2112093832, 2120770621, 2129409929, 2138012079,
   2146577389, 2155106173, 2163598742, 2172055401, 2180476453, 2188862197, 2197212927,
   2205528935, 2213811142, 2222060449, 2230277728, 2238463828, 2246619573, 2254745763,
   2262843175, 2270912564, 2278954664, 2286970188, 2294959829, 2302924261, 2310864139,
   2318780099, 2326672761, 2334542727, 2342390582, 2350216897, 2358022225, 2365807105,
   2373572062, 2381317607, 2389044236, 2396752432, 2404442666, 2412115396, 2419771068,
   2427410115, 2435032961, 2442640017, 2450231684, 2457808352, 2465370401, 2472918201,
   2480452113, 2487972489, 2495479670, 2502973990, 2510455774, 2517925339, 2525382993,
   2532829037, 2540263764, 2547687459, 2555100401, 2562502862, 2569895105, 2577277389,
   2584649965, 2592013078, 2599366967, 2606711865, 2614047999, 2621375590, 2628694855,
   2636006004, 2643309243, 2650604772, 2657892786, 2665173477, 2672447029, 2679713625,
   2686973441, 2694226649, 2701473418, 2708713912, 2715948292, 2723176713, 2730399328,
   2737616285, 2744827730, 2752033804, 2759234645, 2766430388, 2773621164, 2780807102,
   2787988326, 2795164959, 2802337120, 2809504925, 2816668487, 2823827917, 2830983323,
   2838134810, 2845282481, 2852426437, 2859566775, 2866703590, 2873836976, 2880967024,
   2888093822, 2895217457, 2902338013, 2909455572, 2916570215, 2923682020, 2930791064,
   2937897421, 2945001164, 2952102364, 2959201090, 2966297409, 2973391388, 2980483091,
   2987572580, 2994659917, 3001745161, 3008828370, 3015909601, 3022988909, 3030066348,
   3037141971, 3044215829, 3051287972, 3058358448, 3065427305, 3072494589]

/-- Upper table for `A⁻` at `k/80`, scaled by `10⁹`. -/
def tAmU : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 24845680, 49386481, 73629796, 97582751, 121252219, 144644832, 167766992,
   190624882, 213224474, 235571541, 257671664, 279530241, 301152495, 322543482, 343708096,
   364651079, 385377025, 405890385, 426195477, 446296488, 466197479, 485902391, 505415051,
   524739174, 543878369, 562836141, 581615898, 600220952, 618654524, 636919746, 655019665,
   672957246, 690735375, 708356863, 725824445, 743140787, 760308486, 777330071, 794208009,
   810944704, 827542501, 844003686, 860330489, 876525087, 892589604, 908526112, 924336636,
   940023152, 955587590, 971031836, 986357732, 1001567078, 1016661633, 1031643117, 1046513211,
   1061273560, 1075925772, 1090471419, 1104912041, 1119249143, 1133484199, 1147618652,
   1161653913, 1175591365, 1189432362, 1203178229, 1216830266, 1230389744, 1243857911,
   1257235988, 1270525172, 1283726636, 1296841532, 1309870987, 1322816107, 1335677977,
   1348457661, 1361156202, 1373774625, 1386313934, 1398775115, 1411159135, 1423466944,
   1435699475, 1447857643, 1459942346, 1471954467, 1483894872, 1495764413, 1507563926,
   1519294233, 1530956140, 1542550441, 1554077915, 1565539328, 1576935432, 1588266968,
   1599534664, 1610739234, 1621881382, 1632961800, 1643981168, 1654940155, 1665839419,
   1676679608, 1687461358, 1698185296, 1708852039, 1719462194, 1730016358, 1740515118,
   1750959054, 1761348735, 1771684722, 1781967567, 1792197813, 1802375996, 1812502644,
   1822578275, 1832603401, 1842578526, 1852504146, 1862380750, 1872208820, 1881988830,
   1891721248, 1901406535, 1911045146, 1920637528, 1930184122, 1939685364, 1949141682,
   1958553499, 1967921232, 1977245292, 1986526085, 1995764010, 2004959461, 2014112828,
   2023224493, 2032294835, 2041324227, 2050313037, 2059261628, 2068170359, 2077039583,
   2085869649, 2094660901, 2103413679, 2112128318, 2120805149, 2129444499, 2138046690,
   2146612040, 2155140864, 2163633472, 2172090170, 2180511260, 2188897042, 2197247810,
   2205564178, 2213846745, 2222096411, 2230314050, 2238500509, 2246656613, 2254783161,
   2262880931, 2270950678, 2278993136, 2287009017, 2294999015, 2302963804, 2310904038,
   2318820354, 2326713372, 2334583693, 2342431903, 2350258572, 2358064254, 2365849488,
   2373614798, 2381360695, 2389087675, 2396796222, 2404486806, 2412159886, 2419815907,
   2427455303, 2435078497, 2442685900, 2450277913, 2457854927, 2465417321, 2472965466,
   2480499722, 2488020441, 2495527965, 2503022627, 2510504753, 2517974659, 2525432653,
   2532879036, 2540314102, 2547738135, 2555151415, 2562554212, 2569946791, 2577329410,
   2584702320, 2592065767, 2599419989, 2606765219, 2614101684, 2621429606, 2628749201,
   2636060680, 2643364248, 2650660105, 2657948447, 2665229464, 2672503342, 2679770263,
   2687030403, 2694283935, 2701531027, 2708771844, 2716006545, 2723235287, 2730458222,
   2737675499, 2744887263, 2752093655, 2759294814, 2766490874, 2773681966, 2780868219,
   2788049758, 2795226705, 2802399179, 2809567296, 2816731170, 2823890911, 2831046628,
   2838198425, 2845346406, 2852490670, 2859631316, 2866768439, 2873902132, 2881032486,
   2888159589, 2895283528, 2902404388, 2909522250, 2916637195, 2923749302, 2930858647,
   2937965304, 2945069347, 2952170846, 2959269870, 2966366487, 2973460763, 2980552762,
   2987642547, 2994730179, 3001815717, 3008899220, 3015980744, 3023060345, 3030138076,
   3037213990, 3044288139, 3051360572, 3058431338, 3065500484, 3072568057]

/-- Lower table for `A⁺` at `k/80`, scaled by `10⁹`. -/
def tApL : List ℕ :=
  [2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000076681, 2000305796, 2000683616, 2001206524,
   2001871011, 2002673673, 2003611206, 2004680404, 2005878153, 2007201429, 2008647295,
   2010212897, 2011895461, 2013692291, 2015600766, 2017618337, 2019742525, 2021970918,
   2024301170, 2026730998, 2029258178, 2031880546, 2034595995, 2037402473, 2040297981,
   2043280571, 2046348346, 2049499456, 2052732099, 2056044518, 2059434999, 2062901872,
   2066443506, 2070058313, 2073744741, 2077501277, 2081326445, 2085218803, 2089176944,
   2093199495, 2097285115, 2101432494, 2105640352, 2109907441, 2114232539, 2118614455,
   2123052022, 2127544102, 2132089582, 2136687374, 2141336414, 2146035662, 2150784101,
   2155580737, 2160424597, 2165314730, 2170250205, 2175230111, 2180253558, 2185319674,
   2190427605, 2195576517, 2200765592, 2205994030, 2211261047, 2216565877, 2221907769,
   2227285987, 2232699810, 2238148534, 2243631467, 2249147932, 2254697266, 2260278819,
   2265891954, 2271536047, 2277210487, 2282914674, 2288648020, 2294409950, 2300199899,
   2306017313, 2311861650, 2317732378, 2323628974, 2329550927, 2335497734, 2341468904,
   2347463953, 2353482408, 2359523804, 2365587684, 2371673602, 2377781118, 2383909802,
   2390059230, 2396228988, 2402418669, 2408627872, 2414856206, 2421103285, 2427368731,
   2433652173, 2439953246, 2446271593, 2452606862, 2458958708, 2465326792, 2471710781,
   2478110348, 2484525172, 2490954938, 2497399336, 2503858061, 2510330815, 2516817304,
   2523317239, 2529830336, 2536356317, 2542894909, 2549445842, 2556008851, 2562583677,
   2569170064, 2575767762, 2582376523, 2588996105, 2595626270, 2602266783, 2608917414,
   2615577936, 2622248127, 2628927767, 2635616641, 2642314538, 2649021249, 2655736570,
   2662460299, 2669192239, 2675932194, 2682679973, 2689435388, 2696198254, 2702968388,
   2709745611, 2716529747, 2723320622, 2730118066, 2736921911, 2743731991, 2750548145,
   2757370212, 2764198035, 2771031460, 2777870334, 2784714507, 2791563832, 2798418164,
   2805277360, 2812141279]

/-- Upper table for `A⁺` at `k/80`, scaled by `10⁹`. -/
def tApU : List ℕ :=
  [2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000, 2000000000,
   2000000000, 2000000000, 2000000000, 2000077882, 2000308171, 2000687138, 2001211167,
   2001876751, 2002680486, 2003619069, 2004689295, 2005888050, 2007212312, 2008659143,
   2010225691, 2011909182, 2013706921, 2015616288, 2017634734, 2019759781, 2021989017,
   2024320097, 2026750737, 2029278715, 2031901867, 2034618086, 2037425321, 2040321573,
   2043304895, 2046373390, 2049525208, 2052758548, 2056071652, 2059462808, 2062930344,
   2066472632, 2070088082, 2073775144, 2077532305, 2081358088, 2085251052, 2089209791,
   2093232931, 2097319131, 2101467082, 2105675505, 2109943151, 2114268799, 2118651256,
   2123089358, 2127581966, 2132127967, 2136726273, 2141375820, 2146075569, 2150824503,
   2155621628, 2160465971, 2165356581, 2170292527, 2175272899, 2180296806, 2185363376,
   2190471756, 2195621112, 2200810626, 2206039498, 2211306945, 2216612199, 2221954510,
   2227333143, 2232747377, 2238196507, 2243679842, 2249196705, 2254746432, 2260328374,
   2265941895, 2271586370, 2277261187, 2282965748, 2288699465, 2294461762, 2300252074,
   2306069848, 2311914541, 2317785621, 2323682566, 2329604865, 2335552015, 2341523525,
   2347518911, 2353537699, 2359579425, 2365643633, 2371729875, 2377837713, 2383966716,
   2390116461, 2396286533, 2402476524, 2408686036, 2414914675, 2421162057, 2427427804,
   2433711544, 2440012913, 2446331553, 2452667113, 2459019247, 2465387617, 2471771890,
   2478171739, 2484586843, 2491016886, 2497461559, 2503920558, 2510393583, 2516880341,
   2523380543, 2529893906, 2536420151, 2542959004, 2549510196, 2556073463, 2562648545,
   2569235186, 2575833136, 2582442148, 2589061979, 2595692391, 2602333149, 2608984023,
   2615644787, 2622315218, 2628995097, 2635684208, 2642382340, 2649089285, 2655804838,
   2662528798, 2669260967, 2676001150, 2682749156, 2689504796, 2696267885, 2703038241,
   2709815685, 2716600040, 2723391133, 2730188794, 2736992854, 2743803148, 2750619514,
   2757441793, 2764269826, 2771103460, 2777942541, 2784786921, 2791636451, 2798490987,
   2805350386, 2812214507]

def AmL (k : ℕ) : ℕ := tAmL.getD k 0
def AmU (k : ℕ) : ℕ := tAmU.getD k 0
def ApL (k : ℕ) : ℕ := tApL.getD k 0
def ApU (k : ℕ) : ℕ := tApU.getD k 0

theorem of_ball {P : ℕ → Prop} {a b : ℕ} (h : ∀ k < b, a ≤ k → P k) :
    ∀ k, a ≤ k → k < b → P k := fun k h1 h2 => h k h2 h1

theorem of_ball_split {P : ℕ → Prop} {a m b : ℕ}
    (h1 : ∀ k < m, a ≤ k → P k) (h2 : ∀ k < b, m ≤ k → P k) :
    ∀ k, a ≤ k → k < b → P k := fun k h1k hkb =>
  if h : k < m then h1 k h h1k else h2 k hkb (by omega)

theorem chk_Am1 : ∀ k < 240, 160 ≤ k →
    chkLc (AmL (k + 1)) (AmL k) (ApL (k - 80)) (k - 80) = true ∧
    chkUc (AmU (k + 1)) (AmU k) (ApU (k - 80)) (k - 80) = true := by decide +kernel

theorem chk_Ap2 : ∀ k < 400, 240 ≤ k →
    chkL (ApL (k + 1)) (ApL k) (AmL (k - 80)) (ApL (k - 2 * 80)) (k - 80) (k - 2 * 80) = true ∧
    chkU (ApU (k + 1)) (ApU k) (AmU (k - 80)) (ApU (k - 2 * 80 + 1)) (k - 80) (k - 2 * 80) = true := by
  decide +kernel

theorem chk_Am2 : ∀ k < 438, 240 ≤ k →
    chkL (AmL (k + 1)) (AmL k) (ApL (k - 80)) (AmL (k - 2 * 80)) (k - 80) (k - 2 * 80) = true ∧
    chkU (AmU (k + 1)) (AmU k) (ApU (k - 80)) (AmU (k - 2 * 80 + 1)) (k - 80) (k - 2 * 80) = true := by
  decide +kernel

theorem tab_A_base : (∀ k < 161, 80 ≤ k → AmL k = 0 ∧ AmU k = 0) ∧
    (∀ k < 241, 80 ≤ k → ApL k = 2000000000 ∧ ApU k = 2000000000) := by decide +kernel

section OmegaTables
variable {ωp ωm : ℝ → ℝ} (hω : IsOmegaPair ωp ωm)
include hω

theorem TB_Am_base (k : ℕ) (h1 : 80 ≤ k) (h2 : k ≤ 160) :
    TB (fun x => x * ωm x) 80 1000000000 AmL AmU k := by
  obtain ⟨hL, hU⟩ := tab_A_base.1 k (by omega) h1
  have hk : (k : ℝ) / 80 ≤ 2 := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (show k ≤ 160 by omega)
  unfold TB; rw [hL, hU]; simp only [Nat.cast_ofNat]
  rw [Am_zero hω hk (by positivity)]; simp

theorem TB_Ap_base (k : ℕ) (h1 : 80 ≤ k) (h2 : k ≤ 240) :
    TB (fun x => x * ωp x) 80 1000000000 ApL ApU k := by
  obtain ⟨hL, hU⟩ := tab_A_base.2 k (by omega) h1
  have hk : (k : ℝ) / 80 ≤ 3 := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast (show k ≤ 240 by omega)
  have hk0 : 0 < (k : ℝ) / 80 := by
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  unfold TB; rw [hL, hU]; simp only [Nat.cast_ofNat]
  rw [Ap_two hω hk hk0]; norm_num

theorem TB_Am1 (k : ℕ) (h1 : 160 ≤ k) (h2 : k ≤ 240) :
    TB (fun x => x * ωm x) 80 1000000000 AmL AmU k := by
  refine level_ind_const (f := fun x => x * ωp x) (Lf := ApL) (Uf := ApU) (N := 240)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ (TB_Am_base hω 160 (by norm_num) le_rfl)
    (of_ball chk_Am1) k h1 h2
  · intro a b ha hab
    exact (omega_delay hω (by norm_num at ha; linarith) hab).1
  · intro x y hx hy
    norm_num at hx hy
    rw [Ap_two hω (by linarith [hx.2]) (by linarith [hx.1]),
      Ap_two hω (by linarith [hy.2]) (by linarith [hy.1])]
  · intro j hj1 hj2
    exact TB_Ap_base hω j (by omega) (by omega)

theorem TB_Am2a (k : ℕ) (h1 : 240 ≤ k) (h2 : k ≤ 320) :
    TB (fun x => x * ωm x) 80 1000000000 AmL AmU k := by
  refine level_ind (f := fun x => x * ωp x) (e := fun x => x * ωm x) (Lf := ApL) (Uf := ApU)
    (Le := AmL) (Ue := AmU) (N := 320) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    (Ap_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num)))
    (Am_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num))) ?_ ?_ (TB_Am1 hω 240 (by norm_num) le_rfl)
    (fun k hk1 hk2 => chk_Am2 k (by omega) hk1) k h1 h2
  · intro a b ha hab
    exact (omega_delay hω (by norm_num at ha; linarith) hab).1
  · intro p x hp hpx
    exact (omega_delay hω (by norm_num at hp; linarith) hpx).2
  · intro j hj1 hj2; exact TB_Ap_base hω j (by omega) (by omega)
  · intro i hi1 hi2
    exact ⟨TB_Am_base hω i (by omega) (by omega), TB_Am_base hω (i + 1) (by omega) (by omega)⟩

theorem TB_Am_upto320 (k : ℕ) (h1 : 80 ≤ k) (h2 : k ≤ 320) :
    TB (fun x => x * ωm x) 80 1000000000 AmL AmU k := by
  rcases le_or_gt k 160 with h | h
  · exact TB_Am_base hω k h1 h
  rcases le_or_gt k 240 with h' | h'
  · exact TB_Am1 hω k h.le h'
  · exact TB_Am2a hω k h'.le h2

theorem TB_Ap2 (k : ℕ) (h1 : 240 ≤ k) (h2 : k ≤ 400) :
    TB (fun x => x * ωp x) 80 1000000000 ApL ApU k := by
  refine level_ind (f := fun x => x * ωm x) (e := fun x => x * ωp x) (Lf := AmL) (Uf := AmU)
    (Le := ApL) (Ue := ApU) (N := 400) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    (Am_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num)))
    (Ap_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num))) ?_ ?_
    (TB_Ap_base hω 240 (by norm_num) le_rfl) (of_ball chk_Ap2) k h1 h2
  · intro a b ha hab
    exact (omega_delay hω (by norm_num at ha; linarith) hab).2
  · intro p x hp hpx
    exact (omega_delay hω (by norm_num at hp; linarith) hpx).1
  · intro j hj1 hj2; exact TB_Am_upto320 hω j (by omega) (by omega)
  · intro i hi1 hi2
    exact ⟨TB_Ap_base hω i (by omega) (by omega), TB_Ap_base hω (i + 1) (by omega) (by omega)⟩

theorem TB_Am2b (k : ℕ) (h1 : 320 ≤ k) (h2 : k ≤ 438) :
    TB (fun x => x * ωm x) 80 1000000000 AmL AmU k := by
  refine level_ind (f := fun x => x * ωp x) (e := fun x => x * ωm x) (Lf := ApL) (Uf := ApU)
    (Le := AmL) (Ue := AmU) (N := 438) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
    (Ap_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num)))
    (Am_mono hω |>.mono (Ici_subset_Ici.mpr (by norm_num))) ?_ ?_
    (TB_Am2a hω 320 (by norm_num) le_rfl)
    (fun k hk1 hk2 => chk_Am2 k (by omega) (by omega)) k h1 h2
  · intro a b ha hab
    exact (omega_delay hω (by norm_num at ha; linarith) hab).1
  · intro p x hp hpx
    exact (omega_delay hω (by norm_num at hp; linarith) hpx).2
  · intro j hj1 hj2
    rcases le_or_gt j 240 with h | h
    · exact TB_Ap_base hω j (by omega) h
    · exact TB_Ap2 hω j h.le (by omega)
  · intro i hi1 hi2
    exact ⟨TB_Am_upto320 hω i (by omega) (by omega), TB_Am_upto320 hω (i + 1) (by omega) (by omega)⟩

omit hω in
theorem tab_A_vals : AmL 438 = 3072494589 ∧ AmU 438 = 3072568057 ∧ ApL 358 = 2529830336 ∧
    ApU 358 = 2529893906 ∧ AmL 278 = 1812469840 ∧ AmU 280 = 1832603401 := by decide +kernel

/-- **`ω⁻(sθ)` certified**: for the parameters `θ = 0.1635`, `s = 33.5` of the proof of
Theorem 1.2, `sθ = 5.47725` and `ω⁻(5.47725) ∈ [0.56118, 0.56121]`, exactly the printed
enclosure of page 31. The certificate gives `[0.5611879, 0.5612014]`. -/
theorem omega_minus_bounds :
    (0.56118 : ℝ) ≤ ωm (0.1635 * 33.5) ∧ ωm (0.1635 * 33.5) ≤ 0.56121 := by
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := tab_A_vals
  have hβ : (0.1635 : ℝ) * 33.5 = 21909 / 4000 := by norm_num
  rw [hβ]
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 21909 / 4000 := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 438 / 80 := ⟨_, rfl⟩
  rw [← hβdef]
  have ha : 1 < a := by norm_num [hadef]
  have hab : a ≤ β := by norm_num [hadef, hβdef]
  have hA438 := TB_Am2b hω 438 (by norm_num) le_rfl
  have hP358 := TB_Ap2 hω 358 (by norm_num) (by norm_num)
  have hM278 := TB_Am_upto320 hω 278 (by norm_num) (by norm_num)
  have hM280 := TB_Am_upto320 hω 280 (by norm_num) (by norm_num)
  unfold TB at hA438 hP358 hM278 hM280
  rw [v1, v2] at hA438; rw [v3, v4] at hP358; rw [v5] at hM278; rw [v6] at hM280
  norm_num at hA438 hP358 hM278 hM280
  rw [show (219 : ℝ) / 40 = a by rw [hadef]; norm_num] at hA438
  have e358 : (179 : ℝ) / 40 = a - 1 := by norm_num [hadef]
  have e278 : (139 : ℝ) / 40 = a - 1 - 1 := by norm_num [hadef]
  rw [e358] at hP358; rw [e278] at hM278
  -- increments of `A⁺` on `[a-1, β-1]`
  have hp : 1 < a - 1 := by norm_num [hadef]
  have hpq : a - 1 ≤ β - 1 := by linarith
  have hinc := incr (f := fun x => x * ωp x) (e := fun x => x * ωm x) hp hpq
    (fun x hx => (omega_delay hω (by norm_num [hadef]) hx.1).2)
    (Am_mono hω |>.mono fun x hx => by simp only [mem_Ici]; norm_num [hadef] at hx ⊢; linarith [hx.1])
    (Am_nonneg hω (by norm_num [hadef]))
  have hq2 : β - 1 - 1 ≤ 7 / 2 := by norm_num [hβdef]
  have hAmq : (β - 1 - 1) * ωm (β - 1 - 1) ≤ 7 / 2 * ωm (7 / 2) :=
    Am_mono hω (by simp only [mem_Ici]; norm_num [hβdef]) (by simp only [mem_Ici]; norm_num) hq2
  obtain ⟨lo, hlo_def⟩ : ∃ lo : ℝ, lo = 2529830336 / 1000000000 := ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi : ℝ, hi = 2529893906 / 1000000000 := ⟨_, rfl⟩
  obtain ⟨dlo, hdlo_def⟩ : ∃ dlo : ℝ, dlo = 1812469840 / 1000000000 / (β - 1 - 1) := ⟨_, rfl⟩
  obtain ⟨dhi, hdhi_def⟩ : ∃ dhi : ℝ, dhi = 1832603401 / 1000000000 / (a - 1 - 1) := ⟨_, rfl⟩
  have hβ2 : 0 < β - 1 - 1 := by norm_num [hβdef]
  have ha2 : 0 < a - 1 - 1 := by norm_num [hadef]
  have hlo : ∀ u ∈ Icc a β, lo + dlo * (u - a) ≤ (fun x => x * ωp x) (u - 1) := by
    intro u hu
    have hx : u - 1 ∈ Icc (a - 1) (β - 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 := (hinc (u - 1) hx).1
    simp only at h1 ⊢
    have hd : dlo ≤ (a - 1 - 1) * ωm (a - 1 - 1) / (β - 1 - 1) := by
      rw [hdlo_def]; exact div_le_div_of_nonneg_right (by linarith [hM278.1]) hβ2.le
    have hu0 : 0 ≤ u - a := by linarith [hu.1]
    have := mul_le_mul_of_nonneg_left hd hu0
    have hua : u - 1 - (a - 1) = u - a := by ring
    rw [hua] at h1
    linarith [hP358.1, hlo_def]
  have hhi : ∀ u ∈ Icc a β, (fun x => x * ωp x) (u - 1) ≤ hi + dhi * (u - a) := by
    intro u hu
    have hx : u - 1 ∈ Icc (a - 1) (β - 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 := (hinc (u - 1) hx).2
    simp only at h1 ⊢
    have hd : (β - 1 - 1) * ωm (β - 1 - 1) / (a - 1 - 1) ≤ dhi := by
      rw [hdhi_def]; exact div_le_div_of_nonneg_right (by linarith [hM280.2]) ha2.le
    have hu0 : 0 ≤ u - a := by linarith [hu.1]
    have := mul_le_mul_of_nonneg_left hd hu0
    have hua : u - 1 - (a - 1) = u - a := by ring
    rw [hua] at h1
    linarith [hP358.2, hhi_def]
  have hy : 1 < (β - 1) / (a - 1) := by norm_num [hadef, hβdef]
  have hΛL := two_mul_div_le_log hy
  have hΛU := log_le_half_sub_inv hy.le
  obtain ⟨s1, s2⟩ := dstep (g := fun x => x * ωm x) (f := fun x => x * ωp x) ha hab
    (omega_delay hω (by norm_num [hadef]) hab).1
    (Ap_mono hω |>.mono fun x hx => by simp only [mem_Ici]; norm_num [hadef] at hx ⊢; linarith [hx.1])
    hlo hhi hΛL hΛU (by rw [hlo_def]; positivity) (by rw [hhi_def]; positivity)
    (by rw [hdlo_def]; positivity) (by rw [hdhi_def]; positivity)
  have hβpos : (0 : ℝ) < β := by norm_num [hβdef]
  have hω' : ωm β = β * ωm β / β := by field_simp
  rw [hω']
  constructor
  · rw [le_div_iff₀ hβpos]
    have : (0.56118 : ℝ) * β ≤ 3072494589 / 1000000000 + lo * (2 * ((β - 1) / (a - 1) - 1) /
        ((β - 1) / (a - 1) + 1)) + dlo * (β - a - (a - 1) * (((β - 1) / (a - 1) -
        ((β - 1) / (a - 1))⁻¹) / 2)) := by
      rw [hlo_def, hdlo_def]; norm_num [hadef, hβdef]
    linarith [hA438.1]
  · rw [div_le_iff₀ hβpos]
    have : 3072568057 / 1000000000 + hi * (((β - 1) / (a - 1) - ((β - 1) / (a - 1))⁻¹) / 2) +
        dhi * (β - a - (a - 1) * (2 * ((β - 1) / (a - 1) - 1) / ((β - 1) / (a - 1) + 1))) ≤
        (0.56121 : ℝ) * β := by
      rw [hhi_def, hdhi_def]; norm_num [hadef, hβdef]
    linarith [hA438.2]

end OmegaTables

end LeanLab.Akeno2026.SieveFns
