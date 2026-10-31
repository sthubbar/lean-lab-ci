/-
U-1522, PC 20261025T1603Z-10248, T2 FRONTIER, idea I-0126. AI-written Lean code, Claude, 2026-10-25.
Goldbach numbers in short intervals under RH: the smoothed mean square at the centre x/2 with an
unequal AM-GM split lowers the pairing constant from 4.394 (U1348, cumulative J and Abel
summation) to 1/(2 log 2 - 1) ≈ 2.5887, so the lab's 4.45 log² x would become 2.62 log² x.
Source: ChirreHagen2025 P0075 Section 5 as the lab rebuilt it, U1348Bilinear.lean; the smoothed
mean square of I-5170, SmoothY.interval_P_le, whose weight `W(u) = 1 (u ≤ 1), u^-4 (u > 1)`
holds at every centre `X` with the same constant as the cumulative `J(X)`.
Pairing: no Goldbach number in `(x, x + δx]` gives `A(t) A(x - t) = 0`, `A(t) = θ((1+δ)t) - θ(t)`.
Weight `U(t/x) = √(W(2t/x) W(2(x-t)/x))` on `[x/64, 63x/64]`; the split
`U |E(t)E(x-t)| ≤ (W(2t/x) E(t)² + W(2(x-t)/x) E(x-t)²)/2` puts weight exactly `W(t/(x/2))`
on `E(t)²`, so the error side is one smoothed mean square at `X = x/2`, at most `c δ L² x²/4`,
while the main side is `δ² x³ (log 2 - 1/2)/2`.
CONDITIONAL inputs, named: `WeightedJθ c`, the θ form of the lab's smoothed bound (under RH it
follows from the ChirreHagen2025 zero inputs by the Fatou step of A_sq_le_u6806 with `W` kept, not
done here), and `|θ u - u| ≤ u/10^6` for `u ≥ 10^16` (lab: Schoenfeld under RH, ThetaRel6).
The six route leaves are proved in CODEX task79. Binary Goldbach is OPEN; this is a conditional explicit constant.
-/
import Mathlib
import LeanLab.ChirreHagen2025.Bilinear

namespace LeanLab.Routes.U1522

open Real MeasureTheory Set Chebyshev

/-- The smoothing weight `W(r) = 1` for `r ≤ 1`, `r^-4` for `r > 1`, of I-5170. Unit U-1522. -/
noncomputable def Wt (r : ℝ) : ℝ := if r ≤ 1 then 1 else (r ^ 4)⁻¹

/-- `A(δ, t) = θ((1+δ)t) - θ(t)`. Unit U-1522. -/
noncomputable def Aθ (δ t : ℝ) : ℝ := θ ((1 + δ) * t) - θ t

/-- `E(δ, y) = θ((1+δ)y) - θ(y) - δy`. Unit U-1522. -/
noncomputable def Eθ (δ y : ℝ) : ℝ := θ ((1 + δ) * y) - θ y - δ * y

/-- The pairing weight `U(s) = √(W(2s) W(2(1-s)))`. Unit U-1522. -/
noncomputable def Ugm (s : ℝ) : ℝ := Real.sqrt (Wt (2 * s) * Wt (2 * (1 - s)))

/-- The cross term `δ ∫ U(t/x) (t E(x-t) + (x-t) E(t)) dt` over `[x/64, 63x/64]`. Unit U-1522. -/
noncomputable def crossT (x δ : ℝ) : ℝ :=
  δ * ∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t)

/-- CONDITIONAL input, named: the smoothed θ mean square at every centre `X ≥ X0`,
`∫_{y > 2} E(δ, y)² W(y/X) dy ≤ c δ log²(2.0001/δ) X²` for `0 < δ ≤ δ0`. Under RH the lab's
interval_P_le and the Fatou step give this for ψ with c = 1.0068 (A_sq_le_u6806 restricted to
`W = 1`); the θ form with c = 1.0099 is the next leaf, not in this file. Unit U-1522. -/
def WeightedJθ (c X0 δ0 : ℝ) : Prop :=
  ∀ X δ : ℝ, X0 ≤ X → 0 < δ → δ ≤ δ0 →
    IntegrableOn (fun y => Eθ δ y ^ 2 * Wt (y / X)) (Ioi 2) ∧
    ∫ y in Ioi 2, Eθ δ y ^ 2 * Wt (y / X) ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2

/-- A Goldbach number, a sum of two odd primes, in `(a, b]`. Unit U-1522. -/
def GoldbachIn (a b : ℝ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ a < ((p + q : ℕ) : ℝ) ∧ ((p + q : ℕ) : ℝ) ≤ b

/-! ### Proved pieces -/

/-- The unequal AM-GM split: if `u² ≤ F₁ F₂` then `u |ab| ≤ (F₁ a² + F₂ b²)/2`. Unit U-1522. -/
theorem gm_split {u F₁ F₂ a b : ℝ} (hu : 0 ≤ u) (h1 : 0 ≤ F₁) (h2 : 0 ≤ F₂)
    (h : u ^ 2 ≤ F₁ * F₂) : u * |a * b| ≤ (F₁ * a ^ 2 + F₂ * b ^ 2) / 2 := by
  have hs : u ≤ √F₁ * √F₂ := by
    rw [← Real.sqrt_mul h1]
    calc u = √(u ^ 2) := (Real.sqrt_sq hu).symm
      _ ≤ √(F₁ * F₂) := Real.sqrt_le_sqrt h
  have e1 := Real.sq_sqrt h1
  have e2 := Real.sq_sqrt h2
  have ha := sq_abs a
  have hb := sq_abs b
  have hab : |a * b| = |a| * |b| := abs_mul a b
  have s1 := Real.sqrt_nonneg F₁
  have s2 := Real.sqrt_nonneg F₂
  have hA := abs_nonneg a
  have hB := abs_nonneg b
  calc u * |a * b| ≤ (√F₁ * √F₂) * (|a| * |b|) := by
        rw [hab]; exact mul_le_mul_of_nonneg_right hs (mul_nonneg hA hB)
    _ ≤ (F₁ * a ^ 2 + F₂ * b ^ 2) / 2 := by
        nlinarith [sq_nonneg (√F₁ * |a| - √F₂ * |b|)]

/-- The weight identity behind the split: `U(s)² = W(2s) W(2(1-s))`. Unit U-1522. -/
theorem Ugm_sq (s : ℝ) : Ugm s ^ 2 = Wt (2 * s) * Wt (2 * (1 - s)) := by
  have h0 : ∀ r, 0 ≤ Wt r := by
    intro r; unfold Wt; split_ifs <;> positivity
  unfold Ugm
  exact Real.sq_sqrt (mul_nonneg (h0 _) (h0 _))

/-- The main term in closed form: `∫_{1/2}^{1} (1 - t)/t dt = log 2 - 1/2`; on `[1/2, 1]`,
`U(t) t (1 - t) = (1 - t)/(4t)`, so the untruncated main term is `(log 2 - 1/2)/2`. Unit U-1522. -/
theorem int_half_one : ∫ t in (1 / 2 : ℝ)..1, (1 - t) / t = Real.log 2 - 1 / 2 := by
  have e : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, (1 - t) / t = t⁻¹ - 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : t ≠ 0 := by linarith [ht.1]
    field_simp
  rw [intervalIntegral.integral_congr e]
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1]
  rw [intervalIntegral.integral_sub hinv intervalIntegrable_const,
    integral_inv_of_pos (by norm_num) (by norm_num)]
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
  simp
  norm_num

/-- The untruncated pairing constant `κ = 1/(4 · (log 2 - 1/2)/2) = 1/(2 log 2 - 1) < 2.5888`;
the assembly uses the truncated, error-padded 2.592. Unit U-1522. -/
theorem kappa_lt : 1 / (2 * Real.log 2 - 1) < 2.5888 := by
  have h := Real.log_two_gt_d9
  have hpos : 0 < 2 * Real.log 2 - 1 := by linarith
  rw [div_lt_iff₀ hpos]
  linarith

theorem Wt_nonneg (r : ℝ) : 0 ≤ Wt r := by
  unfold Wt
  split_ifs <;> positivity

@[fun_prop]
theorem continuous_Wt : Continuous Wt := by
  unfold Wt
  apply continuous_if_le continuous_id continuous_const continuous_const.continuousOn
  · apply ContinuousOn.inv₀ (continuous_id.pow 4).continuousOn
    intro r hr
    have hr1 : 1 ≤ r := hr
    have hrpos : 0 < r := by linarith
    change r ^ 4 ≠ 0
    exact pow_ne_zero 4 (ne_of_gt hrpos)
  · intro r hr
    change r = 1 at hr
    subst r
    norm_num


@[fun_prop]
theorem continuous_Ugm : Continuous Ugm := by
  unfold Ugm
  exact ((continuous_Wt.comp (continuous_const.mul continuous_id)).mul
    (continuous_Wt.comp (continuous_const.mul (continuous_const.sub continuous_id)))).sqrt

theorem Ugm_symm (s : ℝ) : Ugm (1 - s) = Ugm s := by
  unfold Ugm
  rw [sub_sub_cancel, mul_comm]

theorem Ugm_right {s : ℝ} (hs : 1 / 2 ≤ s) : Ugm s = 1 / (4 * s ^ 2) := by
  have hs0 : 0 < s := by linarith
  have he1 : Wt (2 * s) = ((2 * s) ^ 4)⁻¹ := by
    unfold Wt
    split_ifs with h
    · have he : 2 * s = 1 := by linarith
      simp [he]
    · rfl
  have he2 : Wt (2 * (1 - s)) = 1 := by
    exact if_pos (by linarith)
  unfold Ugm
  rw [he1, he2, mul_one]
  have he : ((2 * s) ^ 4)⁻¹ = (1 / (4 * s ^ 2)) ^ 2 := by field_simp <;> ring
  rw [he, Real.sqrt_sq (by positivity)]

theorem Ugm_left {s : ℝ} (hs : s ≤ 1 / 2) :
    Ugm s = 1 / (4 * (1 - s) ^ 2) := by
  rw [← Ugm_symm s]
  exact Ugm_right (by linarith)

theorem normalized_main_integral :
    (∫ s in (1 / 64 : ℝ)..(63 / 64), Ugm s * (s * (1 - s))) =
      (Real.log (63 / 32) - 31 / 64) / 2 := by
  let f : ℝ → ℝ := fun s => Ugm s * (s * (1 - s))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hr : (∫ s in (1 / 64 : ℝ)..(1 / 2), f s) = ∫ s in (1 / 2 : ℝ)..(63 / 64), f s := by
    calc
      _ = ∫ s in (1 / 64 : ℝ)..(1 / 2), f (1 - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp [f]
        rw [Ugm_symm, sub_sub_cancel]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        norm_num
  have hi : IntervalIntegrable (fun s : ℝ => s⁻¹) volume (1 / 2) (63 / 64) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_inv₀.mono
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hs.1]
  have he : (∫ s in (1 / 2 : ℝ)..(63 / 64), f s) =
      (Real.log (63 / 32) - 31 / 64) / 4 := by
    calc
      _ = ∫ s in (1 / 2 : ℝ)..(63 / 64), (1 / 4 : ℝ) * (s⁻¹ - 1) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le (by norm_num)] at hs
        have hs0 : s ≠ 0 := by linarith [hs.1]
        dsimp [f]
        rw [Ugm_right hs.1]
        field_simp <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hi intervalIntegrable_const,
          integral_inv_of_pos (by norm_num) (by norm_num)]
        norm_num <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (1 / 64) (1 / 2)) (hf.intervalIntegrable (μ := volume) (1 / 2) (63 / 64))
  change (∫ s in (1 / 64 : ℝ)..(63 / 64), f s) = _
  rw [← hadd, hr, he]
  ring

theorem Wt_le_one (r : ℝ) : Wt r ≤ 1 := by
  unfold Wt
  split_ifs with hr
  · exact le_rfl
  · have hr1 : 1 < r := lt_of_not_ge hr
    have hpow : 1 ≤ r ^ 4 := one_le_pow₀ hr1.le
    exact inv_le_one_of_one_le₀ hpow


theorem Ugm_le_one (s : ℝ) : Ugm s ≤ 1 := by
  unfold Ugm
  apply Real.sqrt_le_one.mpr
  simpa using mul_le_mul (Wt_le_one (2 * s)) (Wt_le_one (2 * (1 - s)))
    (Wt_nonneg (2 * (1 - s))) (by norm_num : (0 : ℝ) ≤ 1)

theorem phi_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ Ugm s * (1 - s) ∧ Ugm s * (1 - s) ≤ 1 / 2 := by
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  · by_cases hs : s ≤ 1 / 2
    · have hd : 0 < 1 - s := by linarith
      rw [Ugm_left hs]
      have he : 1 / (4 * (1 - s) ^ 2) * (1 - s) = 1 / (4 * (1 - s)) := by
        field_simp <;> ring
      rw [he, div_le_iff₀ (by positivity : 0 < 4 * (1 - s))]
      linarith
    · have hU := Ugm_le_one s
      nlinarith [mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ 1 - s by linarith)]

theorem phi_scaled_left {p q s : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hs : 0 ≤ s)
    (hqs : q * s ≤ 1 / 2) :
    0 ≤ q * (Ugm (q * s) * (1 - q * s)) - p * (Ugm (p * s) * (1 - p * s)) ∧
    q * (Ugm (q * s) * (1 - q * s)) - p * (Ugm (p * s) * (1 - p * s)) ≤ q - p := by
  have hps : p * s ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_right hpq hs) hqs
  have hd1 : 0 < 1 - p * s := by linarith
  have hd2 : 0 < 1 - q * s := by linarith
  have hden : 1 ≤ 4 * (1 - p * s) * (1 - q * s) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - p * s by linarith)
      (show 0 ≤ 1 / 2 - q * s by linarith)]
  have he : q * (Ugm (q * s) * (1 - q * s)) - p * (Ugm (p * s) * (1 - p * s)) =
      (q - p) / (4 * (1 - p * s) * (1 - q * s)) := by
    rw [Ugm_left hqs, Ugm_left hps]
    have hd1c : 1 - s * p ≠ 0 := by nlinarith
    have hd2c : 1 - s * q ≠ 0 := by nlinarith
    field_simp [ne_of_gt hd1, ne_of_gt hd2, hd1c, hd2c] <;> ring
  rw [he]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hpq) (by positivity)
  · rw [div_le_iff₀ (by positivity : 0 < 4 * (1 - p * s) * (1 - q * s))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hden)]


theorem phi_scaled_right {p q s : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hs : 0 ≤ s)
    (hps : 1 / 2 ≤ p * s) :
    0 ≤ p * (Ugm (p * s) * (1 - p * s)) - q * (Ugm (q * s) * (1 - q * s)) ∧
    p * (Ugm (p * s) * (1 - p * s)) - q * (Ugm (q * s) * (1 - q * s)) ≤ q - p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hs0 : 0 < s := by
    by_contra hn
    have hmul : p * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hn)
    linarith
  have hqs : 1 / 2 ≤ q * s := le_trans hps (mul_le_mul_of_nonneg_right hpq hs)
  have hden : 1 ≤ 4 * p * q * s ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ p * s - 1 / 2 by linarith)
      (show 0 ≤ q * s - 1 / 2 by linarith)]
  have he : p * (Ugm (p * s) * (1 - p * s)) - q * (Ugm (q * s) * (1 - q * s)) =
      (q - p) / (4 * p * q * s ^ 2) := by
    rw [Ugm_right hps, Ugm_right hqs]
    field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hs0] <;> ring
  rw [he]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hpq) (by positivity)
  · rw [div_le_iff₀ (by positivity : 0 < 4 * p * q * s ^ 2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hden)]

theorem phi_dilate {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 ≤ s) :
    |q * (Ugm (q * s) * (1 - q * s)) - Ugm s * (1 - s)| ≤ 1 - q := by
  by_cases hleft : s ≤ 1 / 2
  · have h := phi_scaled_left hq0 hq1 hs (by simpa using hleft)
    simp only [one_mul] at h
    rw [abs_sub_comm, abs_of_nonneg h.1]
    exact h.2
  · by_cases hright : 1 / 2 ≤ q * s
    · have hqpos : 0 < q := by
        by_contra hn
        have hmul : q * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hs
        linarith
      have h := phi_scaled_right hqpos hq1 hs hright
      simp only [one_mul] at h
      rw [abs_of_nonneg h.1]
      exact h.2
    · have hspos : 0 < s := by linarith
      let r := 1 / (2 * s)
      have hrs : r * s = 1 / 2 := by dsimp [r]; field_simp
      have hrpos : 0 < r := by dsimp [r]; positivity
      have hqr : q ≤ r := by
        dsimp [r]
        rw [le_div_iff₀ (by positivity : 0 < 2 * s)]
        linarith
      have hr1 : r ≤ 1 := by
        dsimp [r]
        rw [div_le_one (by positivity : 0 < 2 * s)]
        linarith
      have hl := phi_scaled_left hq0 hqr hs (le_of_eq hrs)
      have hr := phi_scaled_right hrpos hr1 hs (le_of_eq hrs.symm)
      simp only [one_mul] at hr
      rw [abs_le]
      constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

/-! ### Route leaves -/

/-- If both `A(δ, t)` and `A(δ, x - t)` are nonzero, with `t ≥ 2` and `x - t ≥ 2`, there are
primes `p ∈ (t, (1+δ)t]`, `q ∈ (x-t, (1+δ)(x-t)]`, both odd since they exceed 2, and `p + q`
lies in `(x, x + δx]`. Elementary. Unit U-1522. -/
theorem goldbach_of_pair_ne {x δ t : ℝ} (hδ : 0 < δ) (ht : 2 ≤ t) (htx : 2 ≤ x - t)
    (h1 : Aθ δ t ≠ 0) (h2 : Aθ δ (x - t) ≠ 0) : GoldbachIn x (x + δ * x) := by
  have hle : ∀ y : ℝ, 0 ≤ y → y ≤ (1 + δ) * y := by
    intro y hy
    nlinarith
  obtain ⟨p, hp, hpt, hpu⟩ := LeanLab.ChirreHagen2025.prime_of_theta_ne
    (by linarith : 0 ≤ t) (hle t (by linarith)) (sub_ne_zero.mp h1)
  obtain ⟨q, hq, hqt, hqu⟩ := LeanLab.ChirreHagen2025.prime_of_theta_ne
    (by linarith : 0 ≤ x - t) (hle (x - t) (by linarith)) (sub_ne_zero.mp h2)
  have hp2 : p ≠ 2 := by
    intro he
    rw [he] at hpt
    norm_num at hpt
    linarith
  have hq2 : q ≠ 2 := by
    intro he
    rw [he] at hqt
    norm_num at hqt
    linarith
  refine ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    nlinarith


/-- Expanding `A = δt + E` in the vanishing pairing: if `A(t)A(x-t) = 0` on `[x/64, 63x/64]`,
then `δ² ∫ U t(x-t) + cross + ∫ U E(t)E(x-t) = 0`. Integrability: θ is monotone, U is bounded
and piecewise continuous. Unit U-1522. -/
theorem pairing_expand {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hz : ∀ t ∈ Icc (x / 64) (63 * x / 64), Aθ δ t * Aθ δ (x - t) = 0) :
    δ ^ 2 * (∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (t * (x - t))) + crossT x δ
      + ∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (Eθ δ t * Eθ δ (x - t)) = 0 := by
  let a := x / 64
  let b := 63 * x / 64
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have iE : ∀ c d, IntervalIntegrable (Eθ δ) volume c d := by
    intro c d
    exact LeanLab.ChirreHagen2025.Eθ_ii hδ c d
  have iEr : IntervalIntegrable (fun t => Eθ δ (x - t)) volume a b := by
    simpa only [sub_sub_cancel] using (iE (x - a) (x - b)).comp_sub_left x
  have hU : Continuous (fun t => Ugm (t / x)) :=
    continuous_Ugm.comp (continuous_id.div_const x)
  have hM : Continuous (fun t => Ugm (t / x) * (t * (x - t))) := by fun_prop
  have iM := hM.intervalIntegrable (μ := volume) a b
  have iC : IntervalIntegrable
      (fun t => Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t)) volume a b := by
    have i1 : IntervalIntegrable (fun t => Ugm (t / x) * t * Eθ δ (x - t)) volume a b :=
      iEr.continuousOn_mul (hU.mul continuous_id).continuousOn
    have hV : Continuous (fun t : ℝ => Ugm (t / x) * (x - t)) := by fun_prop
    have i2 := (iE a b).continuousOn_mul hV.continuousOn
    convert i1.add i2 using 1 <;> ext t <;> ring
  have he : ∀ t ∈ Set.uIcc a b,
      Ugm (t / x) * (Eθ δ t * Eθ δ (x - t)) =
      -(δ ^ 2 * (Ugm (t / x) * (t * (x - t))) +
        δ * (Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t))) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hz' := hz t ht
    have hA : ∀ y, Aθ δ y = δ * y + Eθ δ y := by intro y; unfold Aθ Eθ; ring
    rw [hA, hA] at hz'
    have he0 := congrArg (fun z : ℝ => Ugm (t / x) * z) hz'
    nlinarith only [he0]
  change δ ^ 2 * (∫ t in a..b, Ugm (t / x) * (t * (x - t))) +
    δ * (∫ t in a..b, Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t)) +
    (∫ t in a..b, Ugm (t / x) * (Eθ δ t * Eθ δ (x - t))) = 0
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_neg,
    intervalIntegral.integral_add (iM.const_mul _) (iC.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring


/-- The bilinear term against one smoothed mean square at `X = x/2`: by `gm_split` with
`F₁ = W(2t/x)`, `F₂ = W(2(x-t)/x)` and `Ugm_sq`, then the reflection `t ↦ x - t`, which maps
`[x/64, 63x/64]` to itself, and `x/64 ≥ 2`. Unit U-1522. -/
theorem ee_le_weighted {x δ : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ)
    (hint : IntegrableOn (fun y => Eθ δ y ^ 2 * Wt (y / (x / 2))) (Ioi 2)) :
    |∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (Eθ δ t * Eθ δ (x - t))|
      ≤ ∫ y in Ioi 2, Eθ δ y ^ 2 * Wt (y / (x / 2)) := by
  have hx0 : x ≠ 0 := by linarith
  let a := x / 64
  let b := 63 * x / 64
  let f : ℝ → ℝ := fun y => Eθ δ y ^ 2 * Wt (y / (x / 2))
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hxa : x - a = b := by dsimp [a, b]; ring
  have hxb : x - b = a := by dsimp [a, b]; ring
  have hf : IntegrableOn f (Ioi 2) := hint
  have ifab : IntervalIntegrable f volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    apply hf.mono_set
    intro t ht
    exact lt_of_le_of_lt ha ht.1
  have ifr : IntervalIntegrable (fun t => f (x - t)) volume a b := by
    simpa only [hxa, hxb, sub_sub_cancel] using ifab.symm.comp_sub_left x
  have iG : IntervalIntegrable (fun t => (f t + f (x - t)) / 2) volume a b :=
    (ifab.add ifr).div_const 2
  have hbnd : |∫ t in a..b, Ugm (t / x) * (Eθ δ t * Eθ δ (x - t))| ≤
      ∫ t in a..b, (f t + f (x - t)) / 2 := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ iG
    filter_upwards [] with t ht
    have hU0 : 0 ≤ Ugm (t / x) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hU0]
    have hgm := gm_split hU0
      (Wt_nonneg (2 * (t / x))) (Wt_nonneg (2 * (1 - t / x)))
      (le_of_eq (Ugm_sq (t / x))) (a := Eθ δ t) (b := Eθ δ (x - t))
    have harg1 : t / (x / 2) = 2 * (t / x) := by field_simp <;> ring
    have harg2 : (x - t) / (x / 2) = 2 * (1 - t / x) := by field_simp <;> ring
    change Ugm (t / x) * |Eθ δ t * Eθ δ (x - t)| ≤
      (Eθ δ t ^ 2 * Wt (t / (x / 2)) + Eθ δ (x - t) ^ 2 * Wt ((x - t) / (x / 2))) / 2
    rw [harg1, harg2]
    nlinarith only [hgm]
  have hreflect : (∫ t in a..b, f (x - t)) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_comp_sub_left, hxb, hxa]
  have heq : (∫ t in a..b, (f t + f (x - t)) / 2) = ∫ t in a..b, f t := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add ifab ifr, hreflect]
    ring
  rw [heq] at hbnd
  apply hbnd.trans
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set hf
  · exact Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (Wt_nonneg _))
  · exact Filter.Eventually.of_forall (fun t ht => lt_of_le_of_lt ha ht.1)


/-- The cross term is small: writing `θ(u) = u + R(u)` the `u` part cancels exactly and
`|cross| = 2δ |∫ R(s)(φ(s/(1+δ))/(1+δ) - φ(s)) ds|` with `φ(t) = U(t/x)(x - t)` on
`[x/64, 63x/64]`; with `|R(u)| ≤ ηu` for `u ≥ x/64` the constant is about 0.5 (gen crossK.py),
stated with 4. Unit U-1522. -/
theorem cross_le {x δ η : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η)
    (hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ η * u) :
    |crossT x δ| ≤ 4 * η * δ ^ 2 * x ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  let a := x / 64
  let b := 63 * x / 64
  let g : ℝ → ℝ := fun t => Ugm (t / x) * (x - t)
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hba : b - a ≤ x := by dsimp [a, b]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hbx : b ≤ x := by dsimp [b]; linarith
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgform : ∀ t, g t = x * (Ugm (t / x) * (1 - t / x)) := by
    intro t
    dsimp [g]
    field_simp <;> ring
  have hgb : ∀ t, 0 ≤ t → t ≤ x → 0 ≤ g t ∧ |g t| ≤ x / 2 := by
    intro t ht0 htx
    have ht := phi_bounds (div_nonneg ht0 hxpos.le) ((div_le_one hxpos).mpr htx)
    rw [hgform]
    constructor
    · exact mul_nonneg hxpos.le ht.1
    · rw [abs_mul, abs_of_pos hxpos, abs_of_nonneg ht.1]
      nlinarith [mul_le_mul_of_nonneg_left ht.2 hxpos.le]
  have hE : ∀ y, a ≤ y → |Eθ δ y| ≤ η * (2 + δ) * y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans ha.le hy
    have hky : a ≤ (1 + δ) * y := by nlinarith
    have h1 := hR ((1 + δ) * y) hky
    have h2 := hR y hy
    have he : Eθ δ y = (θ ((1 + δ) * y) - (1 + δ) * y) - (θ y - y) := by
      unfold Eθ
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  by_cases hdlarge : 3 / 8 ≤ δ
  · have hbnd : |∫ t in a..b, Ugm (t / x) *
        (t * Eθ δ (x - t) + (x - t) * Eθ δ t)| ≤
        (η * (2 + δ) * x ^ 2 / 2) * (b - a) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a) (b := b) (C := η * (2 + δ) * x ^ 2 / 2)
        (f := fun t => Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at h
      apply h
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hxt0 : 0 ≤ x - t := by linarith [ht.2]
      have hxt : a ≤ x - t := by dsimp [a, b] at *; linarith [ht.2]
      have he1 := hE t ht.1.le
      have he2 := hE (x - t) hxt
      have hu0 : 0 ≤ Ugm (t / x) := Real.sqrt_nonneg _
      have hu1 := Ugm_le_one (t / x)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu0]
      calc
        _ ≤ Ugm (t / x) * (|t * Eθ δ (x - t)| + |(x - t) * Eθ δ t|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hu0
        _ ≤ Ugm (t / x) * (2 * η * (2 + δ) * (t * (x - t))) := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hxt0]
          nlinarith [mul_le_mul_of_nonneg_left he2 ht0, mul_le_mul_of_nonneg_left he1 hxt0]
        _ ≤ 2 * η * (2 + δ) * (t * (x - t)) := by
          exact mul_le_of_le_one_left (by positivity) hu1
        _ ≤ η * (2 + δ) * x ^ 2 / 2 := by
          nlinarith [mul_nonneg (show 0 ≤ η * (2 + δ) by positivity) (sq_nonneg (t - x / 2))]
    change |δ * (∫ t in a..b, Ugm (t / x) *
      (t * Eθ δ (x - t) + (x - t) * Eθ δ t))| ≤ _
    rw [abs_mul, abs_of_pos hδ]
    calc
      _ ≤ δ * ((η * (2 + δ) * x ^ 2 / 2) * (b - a)) := mul_le_mul_of_nonneg_left hbnd hδ.le
      _ ≤ δ * ((η * (2 + δ) * x ^ 2 / 2) * x) := by gcongr
      _ ≤ 4 * η * δ ^ 2 * x ^ 3 := by
        have hh : 2 + δ ≤ 8 * δ := by linarith
        have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ η * δ * x ^ 3 / 2 by positivity)
        nlinarith
  · have hdsmall : δ ≤ 3 / 8 := le_of_lt (lt_of_not_ge hdlarge)
    let q : ℝ := 1 / (1 + δ)
    have hk : 0 < 1 + δ := by linarith
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q ≤ 1 := by dsimp [q]; rw [div_le_one hk]; linarith
    have hqrel : q * (1 + δ) = 1 := by dsimp [q]; field_simp
    have hqd : 1 - q ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hq1)]
    have hD : ∀ u, (1 + δ) * a ≤ u → u ≤ b →
        |g (u / (1 + δ)) / (1 + δ) - g u| ≤ δ * x := by
      intro u hu0 hu1
      have hu0' : 0 ≤ u := (lt_of_lt_of_le (mul_pos hk ha) hu0).le
      have hus : 0 ≤ u / x := div_nonneg hu0' hxpos.le
      have hd := phi_dilate hq0 hq1 hus
      have hearg : u / (1 + δ) / x = q * (u / x) := by dsimp [q]; ring
      have he : g (u / (1 + δ)) / (1 + δ) - g u =
          x * (q * (Ugm (q * (u / x)) * (1 - q * (u / x))) - Ugm (u / x) * (1 - u / x)) := by
        rw [hgform, hgform, hearg]
        dsimp [q]
        ring
      rw [he, abs_mul, abs_of_pos hxpos]
      calc
        _ ≤ x * (1 - q) := mul_le_mul_of_nonneg_left hd hxpos.le
        _ ≤ δ * x := by nlinarith
    have iE : ∀ c d, IntervalIntegrable (Eθ δ) volume c d := by
      intro c d
      exact LeanLab.ChirreHagen2025.Eθ_ii hδ c d
    have iEr : IntervalIntegrable (fun t => Eθ δ (x - t)) volume a b := by
      simpa only [sub_sub_cancel] using (iE (x - a) (x - b)).comp_sub_left x
    have hU : Continuous (fun t => Ugm (t / x)) := by fun_prop
    have i1 : IntervalIntegrable (fun t => Ugm (t / x) * t * Eθ δ (x - t)) volume a b :=
      iEr.continuousOn_mul (hU.mul continuous_id).continuousOn
    have i2 := (iE a b).continuousOn_mul hg.continuousOn
    have href : (∫ t in a..b, Ugm (t / x) * t * Eθ δ (x - t)) = ∫ t in a..b, g t * Eθ δ t := by
      calc
        _ = ∫ t in a..b, g (x - t) * Eθ δ (x - t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have hearg : (x - t) / x = 1 - t / x := by field_simp <;> ring
          dsimp [g]
          rw [hearg, Ugm_symm, sub_sub_cancel]
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left (fun u => g u * Eθ δ u) x]
          have he1 : x - b = a := by dsimp [a, b]; ring
          have he2 : x - a = b := by dsimp [a, b]; ring
          rw [he1, he2]
    have hc : crossT x δ = 2 * δ * ∫ t in a..b, g t * Eθ δ t := by
      unfold crossT
      change δ * (∫ t in a..b, Ugm (t / x) *
        (t * Eθ δ (x - t) + (x - t) * Eθ δ t)) = _
      have he : (∫ t in a..b, Ugm (t / x) * (t * Eθ δ (x - t) + (x - t) * Eθ δ t)) =
          (∫ t in a..b, Ugm (t / x) * t * Eθ δ (x - t)) + ∫ t in a..b, g t * Eθ δ t := by
        rw [← intervalIntegral.integral_add i1 i2]
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [g]
        ring
      rw [he, href]
      ring
    let ρ := (11 / 8 : ℝ) * b * η
    have hρ : ∀ u, a ≤ u → u ≤ (1 + δ) * b → |LeanLab.ChirreHagen2025.Rθ u| ≤ ρ := by
      intro u hu0 hu1
      have hr := hR u hu0
      change |θ u - u| ≤ ρ
      dsimp [ρ]
      nlinarith [mul_le_mul_of_nonneg_right hu1 hη, mul_nonneg (show 0 ≤ 3 / 8 - δ by linarith) (mul_nonneg hb.le hη)]
    have hG1 : ∀ u, a ≤ u → u ≤ (1 + δ) * a → |g u| ≤ x / 2 := by
      intro u hu0 hu1
      have hux : u ≤ x := by
        dsimp [a] at hu1
        nlinarith [mul_le_mul_of_nonneg_right hδ1 hxpos.le]
      exact (hgb u (by linarith) hux).2
    have hG2 : ∀ u, b ≤ u → u ≤ (1 + δ) * b → |g (u / (1 + δ)) / (1 + δ)| ≤ x / 2 := by
      intro u hu0 hu1
      have hu0' : 0 ≤ u := by linarith
      have huq0 : 0 ≤ u / (1 + δ) := div_nonneg hu0' hk.le
      have huqx : u / (1 + δ) ≤ x := by
        rw [div_le_iff₀ hk]
        calc
          u ≤ (1 + δ) * x := hu1.trans (mul_le_mul_of_nonneg_left hbx hk.le)
          _ = x * (1 + δ) := mul_comm _ _
      have hh := (hgb (u / (1 + δ)) huq0 huqx).2
      rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
      nlinarith [mul_nonneg hδ.le hxpos.le]
    have hcbd := LeanLab.ChirreHagen2025.cross_bound hg hδ ha
      (by dsimp [a, b]; nlinarith [mul_le_mul_of_nonneg_right hδ1 hxpos.le]) hρ hD hG1 hG2
    change |∫ t in a..b, g t * Eθ δ t| ≤ _ at hcbd
    rw [hc, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * δ)]
    calc
      _ ≤ (2 * δ) * (δ * x * ρ * (b - a) + (x / 2) * ρ * (δ * b) + (x / 2) * ρ * (δ * a)) :=
        mul_le_mul_of_nonneg_left hcbd (by positivity)
      _ ≤ 4 * η * δ ^ 2 * x ^ 3 := by
        dsimp [a, b, ρ]
        have hp : 0 ≤ η * δ ^ 2 * x ^ 3 := by positivity
        nlinarith


/-- The truncated main term: `∫_{x/64}^{63x/64} U(t/x) t(x-t) dt ≥ 0.0965 x³`; the untruncated
value is `x³ (log 2 - 1/2)/2 ≈ 0.096574 x³` by `int_half_one` and symmetry, the two cut ends
cost about `6·10⁻⁵ x³`. Unit U-1522. -/
theorem main_ge {x : ℝ} (hx : 0 < x) :
    0.0965 * x ^ 3 ≤ ∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (t * (x - t)) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hl : (0.677375 : ℝ) ≤ Real.log (63 / 32) := by
    have hrat : (64 / 63 : ℝ) ≤ (1.001971 : ℝ) ^ 8 := by norm_num
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 64 / 63) hrat
    rw [Real.log_pow] at hmono
    norm_num only [Nat.cast_ofNat] at hmono
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.001971)
    have he : Real.log (63 / 32) + Real.log (64 / 63) = Real.log 2 := by
      rw [← Real.log_mul (by norm_num : (63 / 32 : ℝ) ≠ 0) (by norm_num : (64 / 63 : ℝ) ≠ 0)]
      norm_num
    linarith [Real.log_two_gt_d9]
  have he : (∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (t * (x - t))) =
      x ^ 3 * ((Real.log (63 / 32) - 31 / 64) / 2) := by
    calc
      _ = ∫ t in (x / 64)..(63 * x / 64),
          x ^ 2 * (Ugm (t / x) * ((t / x) * (1 - t / x))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        field_simp <;> ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div (fun s => Ugm s * (s * (1 - s))) hxne]
        have ha : x / 64 / x = (1 / 64 : ℝ) := by field_simp
        have hb : 63 * x / 64 / x = (63 / 64 : ℝ) := by field_simp
        rw [ha, hb, normalized_main_integral]
        simp only [smul_eq_mul]
        ring
  rw [he]
  have hp : 0 ≤ x ^ 3 := by positivity
  calc
    0.0965 * x ^ 3 ≤ ((Real.log (63 / 32) - 31 / 64) / 2) * x ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) hp
    _ = x ^ 3 * ((Real.log (63 / 32) - 31 / 64) / 2) := by ring


/-- `δ = 2.62 log² x / x ≤ 10⁻¹³` for `x ≥ 10^18`. Elementary. Unit U-1522. -/
theorem delta_small {x : ℝ} (hx : 10 ^ 18 ≤ x) : 2.62 * Real.log x ^ 2 / x ≤ 1 / 10 ^ 13 := by
  have hx0 : 0 < x := by linarith
  have he2 : Real.exp 2 ≤ (10 : ℝ) ^ 18 := by
    have he := Real.exp_one_lt_d9
    have heq : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring
    rw [heq]
    nlinarith [Real.exp_pos 1]
  have hm := Real.log_div_sqrt_antitoneOn he2 (le_trans he2 hx) hx
  dsimp only at hm
  have hl0 : 0 ≤ Real.log x / Real.sqrt x := by positivity [Real.log_nonneg (by linarith : 1 ≤ x)]
  have hs : Real.sqrt ((10 : ℝ) ^ 18) = 10 ^ 9 := by
    norm_num [Real.sqrt_eq_iff_eq_sq]
  have hl : Real.log ((10 : ℝ) ^ 18) ≤ 42 := by
    rw [Real.log_pow, Real.log_ten_eq]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  rw [hs] at hm
  have hb : Real.log x / Real.sqrt x ≤ 42 / 10 ^ 9 :=
    le_trans hm (div_le_div_of_nonneg_right hl (by positivity))
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have heq : (Real.log x / Real.sqrt x) ^ 2 = Real.log x ^ 2 / x := by
    rw [div_pow, hsx]
  have hp := pow_le_pow_left₀ hl0 hb 2
  rw [heq] at hp
  calc
    2.62 * Real.log x ^ 2 / x = 2.62 * (Real.log x ^ 2 / x) := by ring
    _ ≤ 2.62 * ((42 / 10 ^ 9 : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ 1 / 10 ^ 13 := by norm_num


/-! ### Assembly, real proofs -/

/-- ASSEMBLY. CONDITIONAL ON `WeightedJθ c X0 δ0` and `|θ u - u| ≤ ηu` for `u ≥ x/64`, with
`η ≤ 10⁻⁶`: if `2.592 c log²(2.0001/δ) < δx` then `(x, x + δx]` holds a Goldbach number.
Proof from the leaves above. Unit U-1522. -/
theorem goldbach_of_weighted {c X0 δ0 η x δ : ℝ} (hW : WeightedJθ c X0 δ0) (hc : 0 ≤ c)
    (hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ η * u) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10 ^ 6)
    (hX : X0 ≤ x / 2) (hx : 128 ≤ x) (hδ : 0 < δ) (hδ0 : δ ≤ δ0) (hδ1 : δ ≤ 1)
    (hbig : 2.592 * c * Real.log (2.0001 / δ) ^ 2 < δ * x) : GoldbachIn x (x + δ * x) := by
  by_contra hG
  have hz : ∀ t ∈ Icc (x / 64) (63 * x / 64), Aθ δ t * Aθ δ (x - t) = 0 := by
    intro t ht
    by_contra hne
    rcases mul_ne_zero_iff.mp hne with ⟨h1, h2⟩
    exact hG (goldbach_of_pair_ne hδ (by linarith [ht.1]) (by linarith [ht.2]) h1 h2)
  obtain ⟨hint, hJ⟩ := hW (x / 2) δ hX hδ hδ0
  have hx0 : 0 < x := by linarith
  have e := pairing_expand hx0 hδ hz
  have b2 := ee_le_weighted hx hδ hint
  have b3 := cross_le hx hδ hδ1 hη0 hR
  have d := main_ge hx0
  set I := ∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (t * (x - t)) with hI
  set C := crossT x δ with hC
  set EE := ∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (Eθ δ t * Eθ δ (x - t)) with hEE
  set S := ∫ y in Ioi 2, Eθ δ y ^ 2 * Wt (y / (x / 2)) with hS
  set L := Real.log (2.0001 / δ) with hL
  have nC := neg_abs_le C
  have nE := neg_abs_le EE
  have hd2 : δ ^ 2 * (0.0965 * x ^ 3) ≤ δ ^ 2 * I := mul_le_mul_of_nonneg_left d (sq_nonneg δ)
  have key : δ ^ 2 * x ^ 3 * (0.0965 - 4 * η) ≤ c * δ * L ^ 2 * (x / 2) ^ 2 := by
    have : δ ^ 2 * x ^ 3 * (0.0965 - 4 * η) = δ ^ 2 * (0.0965 * x ^ 3) - 4 * η * δ ^ 2 * x ^ 3 := by
      ring
    rw [this]
    linarith
  have hpos : 0 < δ * x ^ 2 := by positivity
  have k2 : (δ * x ^ 2) * (δ * x * (0.0965 - 4 * η)) ≤ (δ * x ^ 2) * (c * L ^ 2 / 4) := by
    have e1 : (δ * x ^ 2) * (δ * x * (0.0965 - 4 * η)) = δ ^ 2 * x ^ 3 * (0.0965 - 4 * η) := by ring
    have e2 : (δ * x ^ 2) * (c * L ^ 2 / 4) = c * δ * L ^ 2 * (x / 2) ^ 2 := by ring
    rw [e1, e2]; exact key
  have k3 := le_of_mul_le_mul_left k2 hpos
  have hcL : 0 ≤ c * L ^ 2 := mul_nonneg hc (sq_nonneg L)
  have hm : 0 < 0.0965 - 4 * η := by linarith
  have k4 : 2.592 * c * L ^ 2 * (0.0965 - 4 * η) < δ * x * (0.0965 - 4 * η) :=
    mul_lt_mul_of_pos_right hbig hm
  nlinarith [mul_nonneg hcL hη0]

/-- The headline, CONDITIONAL ON `WeightedJθ 1.0099 (10^13) (10^-13)` and
`|θ u - u| ≤ u/10^6` for `u ≥ 10^16`: for every `x ≥ 10^18` a Goldbach number lies in
`(x, x + 2.62 log² x]`. Below 4·10^18 the even check covers every interval of length 2.
The constant: `2.592 · 1.0099 = 2.6177 < 2.62`, against the lab's 4.45. Unit U-1522. -/
theorem goldbach_262_of_weighted (hW : WeightedJθ 1.0099 (10 ^ 13) (1 / 10 ^ 13))
    (hR6 : ∀ u : ℝ, 10 ^ 16 ≤ u → |θ u - u| ≤ u / 10 ^ 6) {x : ℝ} (hx : 10 ^ 18 ≤ x) :
    GoldbachIn x (x + 2.62 * Real.log x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  set δ := 2.62 * Real.log x ^ 2 / x with hδdef
  have hδ : 0 < δ := by positivity
  have hδ13 := delta_small hx
  have hδ1 : δ ≤ 1 := le_trans hδ13 (by norm_num)
  have hδx : δ * x = 2.62 * Real.log x ^ 2 := by rw [hδdef]; field_simp
  have hR : ∀ u : ℝ, x / 64 ≤ u → |θ u - u| ≤ 1 / 10 ^ 6 * u := by
    intro u hu
    have h := hR6 u (by linarith)
    calc |θ u - u| ≤ u / 10 ^ 6 := h
      _ = 1 / 10 ^ 6 * u := by ring
  -- 1 ≤ 2.0001/δ ≤ x, so 0 ≤ L ≤ log x
  have hup : 2.0001 / δ ≤ x := by
    rw [div_le_iff₀ hδ, mul_comm, hδx]; nlinarith
  have hlow : 1 ≤ 2.0001 / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hL0 : 0 ≤ Real.log (2.0001 / δ) := Real.log_nonneg hlow
  have hLx : Real.log (2.0001 / δ) ≤ Real.log x := Real.log_le_log (by linarith) hup
  have hL2 : Real.log (2.0001 / δ) ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ hL0 hLx 2
  have hbig : 2.592 * 1.0099 * Real.log (2.0001 / δ) ^ 2 < δ * x := by
    rw [hδx]; nlinarith
  have h := goldbach_of_weighted hW (by norm_num) hR (by norm_num) le_rfl
    (by linarith) (by linarith) hδ hδ13 hδ1 hbig
  rwa [hδx] at h

/-- Vacuity of the split lemma: `u = 1/4`, `F₁ = 1`, `F₂ = 1/16`, the values of `U`, `W(2t)` and
`W(2(1-t))` at `t = 1/4`, meet `u² ≤ F₁F₂` with equality. Unit U-1522. -/
theorem gm_split_vacuity : (1 / 4 : ℝ) ^ 2 ≤ 1 * (1 / 16) ∧ (0 : ℝ) ≤ 1 / 4 := by norm_num

end LeanLab.Routes.U1522
