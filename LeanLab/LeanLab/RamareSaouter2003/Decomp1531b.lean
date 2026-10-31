import Mathlib
import LeanLab.RamareSaouter2003.Theorem3Smooth
import LeanLab.PNTPort.StrongPNT.ZetaBounds
import LeanLab.PNTPort.ZetaZeros.Sym

/-!
# Ramare-Saouter 2003, main term, log term and the algebra of display (15)

Unit U-1531, run 20261026T0004Z-24325, DECOMPOSE. AI wrote this Lean code, Claude, checked only
by the Lean kernel. Binary Goldbach is OPEN.

After the explicit formula Lemma 4 is applied to `J` on p. 19, three kinds of terms remain: the
main term `int ((e^u - 1)(1 + delta t) X) f`, the zero terms, handled in `Decomp1531a`, and the
term from `-(1/2) log(1 - t^-2)`. This file states LEAF lemmas for the main and log terms, for
the elementary inequalities inside the proof of Lemma 5 on pp. 16 and 17, for the first line of
the proof of Theorem 4 on p. 18, and for the absence of real zeros of zeta in `]0, 1[`.

Assemblies, with real proofs and no sorry of their own, CONDITIONAL ON the leaves:
`display15_of_split`, the inequality of display (15) in the multiplied out form used by the
lab, from a split of the `psi` integral into main, zero and log terms with the zero terms
bounded as in `Decomp1531a`; `near_term_alpha1`, the replacement of `2N(T)/√X` by
`alpha1/√0.999` in (16).
-/

namespace LeanLab.RamareSaouter2003.Decomp1531b

open LeanLab.RamareSaouter2003.Smooth Set Chebyshev

/-- LEAF. Unit U-1531. For `f` continuous and nonnegative on `[0, 1]` and `u, delta, X >= 0`,
`u X ||f||_1` is at most the integral of `(e^u (1 + delta t) X - (1 + delta t) X) f(t)` over
`[0, 1]`; the main term of (13), p. 19. -/
theorem main_term_ge {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) {u δ X : ℝ} (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hX : 0 ≤ X) :
    u * X * (∫ t in (0 : ℝ)..1, f t) ≤
      ∫ t in (0 : ℝ)..1, (Real.exp u * (1 + δ * t) * X - (1 + δ * t) * X) * f t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (hf.const_mul _).intervalIntegrable_of_Icc (by norm_num)
  · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact ContinuousOn.mul (by fun_prop) hf
  · intro t ht
    have hdt : 0 ≤ δ * t := mul_nonneg hδ ht.1
    have hmain : u ≤ (Real.exp u - 1) * (1 + δ * t) := by
      have he := Real.add_one_le_exp u
      nlinarith [mul_nonneg (show 0 ≤ Real.exp u - 1 by linarith) hdt]
    have hx := mul_le_mul_of_nonneg_right hmain hX
    have hf' := mul_le_mul_of_nonneg_right hx (hf0 t ht)
    nlinarith

/-- LEAF. Unit U-1531. For `10^12 <= X <= Z` and `u >= 0`, the difference
`log(1 - 1/(e^u Z)^2) - log(1 - 1/Z^2)` lies in `[0, u/X]`; the elementary inequality on
p. 19 before (13). -/
theorem log_term_le {X Z u : ℝ} (hX : 10 ^ 12 ≤ X) (hZ : X ≤ Z) (hu : 0 ≤ u) :
    0 ≤ Real.log (1 - 1 / (Real.exp u * Z) ^ 2) - Real.log (1 - 1 / Z ^ 2) ∧
      Real.log (1 - 1 / (Real.exp u * Z) ^ 2) - Real.log (1 - 1 / Z ^ 2) ≤ u / X := by
  have hX0 : 0 < X := by linarith
  have hZ0 : 0 < Z := by linarith
  have hZ2 : 1 < Z ^ 2 := by nlinarith
  have he : 0 < Real.exp u := Real.exp_pos _
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have heZ : 0 < Real.exp u * Z := by positivity
  have heZ2 : Z ^ 2 ≤ (Real.exp u * Z) ^ 2 := by
    have hh : Z ≤ Real.exp u * Z := by nlinarith
    nlinarith
  have hB : 0 < 1 - 1 / Z ^ 2 := by
    have hh := (div_lt_one (by positivity : 0 < Z ^ 2)).mpr hZ2
    linarith
  have hAB : 1 - 1 / Z ^ 2 ≤ 1 - 1 / (Real.exp u * Z) ^ 2 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < Z ^ 2) heZ2
    linarith
  have hA : 0 < 1 - 1 / (Real.exp u * Z) ^ 2 := hB.trans_le hAB
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hB hAB)
  · have hlog := Real.log_le_sub_one_of_pos
      (div_pos hA hB)
    rw [Real.log_div hA.ne' hB.ne'] at hlog
    have hid : (1 - 1 / (Real.exp u * Z) ^ 2) / (1 - 1 / Z ^ 2) - 1 =
        (1 - 1 / (Real.exp u) ^ 2) / (Z ^ 2 - 1) := by
      field_simp
      ring
    rw [hid] at hlog
    have hex : Real.exp (-2 * u) = 1 / Real.exp u ^ 2 := by
      rw [show -2 * u = -(u + u) by ring, Real.exp_neg, Real.exp_add]
      ring
    have hnum : 1 - 1 / Real.exp u ^ 2 ≤ 2 * u := by
      have hh := Real.add_one_le_exp (-2 * u)
      rw [hex] at hh
      linarith
    have hden : 2 * X ≤ Z ^ 2 - 1 := by nlinarith
    have hden0 : 0 < Z ^ 2 - 1 := by linarith
    calc
      Real.log (1 - 1 / (Real.exp u * Z) ^ 2) - Real.log (1 - 1 / Z ^ 2) ≤
          (1 - 1 / Real.exp u ^ 2) / (Z ^ 2 - 1) := hlog
      _ ≤ 2 * u / (Z ^ 2 - 1) := div_le_div_of_nonneg_right hnum hden0.le
      _ ≤ 2 * u / (2 * X) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = u / X := by ring

/-- LEAF. Unit U-1531. Integrated form: for `f` continuous and nonnegative on `[0, 1]`,
`10^12 <= X`, `u >= 0` and `delta >= 0`, the integral over `[0, 1]` of one half of
`log(1 - 1/(e^u (1 + delta t) X)^2) - log(1 - 1/((1 + delta t) X)^2)` times `f` is at most
`u/(2X) ||f||_1`; p. 19 before (13). -/
theorem log_term_integral_le {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t) {X u δ : ℝ} (hX : 10 ^ 12 ≤ X) (hu : 0 ≤ u)
    (hδ : 0 ≤ δ) :
    (∫ t in (0 : ℝ)..1, (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + δ * t) * X)) ^ 2) -
        Real.log (1 - 1 / ((1 + δ * t) * X) ^ 2)) * f t) ≤
      u / (2 * X) * ∫ t in (0 : ℝ)..1, f t := by
  let Z : ℝ → ℝ := fun t => (1 + δ * t) * X
  have hX0 : 0 < X := by linarith
  have hZ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : X ≤ Z t := by
    dsimp [Z]
    nlinarith [mul_nonneg hδ ht.1]
  have hZ0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < Z t := hX0.trans_le (hZ t ht)
  have he : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - 1 / (Z t) ^ 2 := by
    have hz := hZ t ht
    have hz0 := hZ0 t ht
    have hsq : 1 < (Z t) ^ 2 := by nlinarith
    have hh := (div_lt_one (by positivity : 0 < (Z t) ^ 2)).mpr hsq
    linarith
  have hA (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - 1 / (Real.exp u * Z t) ^ 2 := by
    have hz := hZ t ht
    have hz0 := hZ0 t ht
    have hprod : Z t ≤ Real.exp u * Z t := by nlinarith
    have hsq : 1 < (Real.exp u * Z t) ^ 2 := by nlinarith
    have hh := (div_lt_one (by positivity : 0 < (Real.exp u * Z t) ^ 2)).mpr hsq
    linarith
  have hZcont : Continuous Z := by dsimp [Z]; fun_prop
  have hcB : ContinuousOn (fun t => Real.log (1 - 1 / (Z t) ^ 2)) (Icc 0 1) := by
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      exact ContinuousOn.div continuousOn_const (hZcont.pow 2).continuousOn
        (fun t ht => pow_ne_zero _ (hZ0 t ht).ne')
    · intro t ht; exact (hB t ht).ne'
  have hcA : ContinuousOn (fun t => Real.log (1 - 1 / (Real.exp u * Z t) ^ 2)) (Icc 0 1) := by
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      exact ContinuousOn.div continuousOn_const ((hZcont.const_mul _).pow 2).continuousOn
        (fun t ht => pow_ne_zero _ (mul_pos (Real.exp_pos _) (hZ0 t ht)).ne')
    · intro t ht; exact (hA t ht).ne'
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact (((hcA.sub hcB).const_mul (1 / 2 : ℝ)).mul hf).intervalIntegrable_of_Icc (by norm_num)
  · exact (hf.const_mul _).intervalIntegrable_of_Icc (by norm_num)
  · intro t ht
    have hh := (log_term_le hX (hZ t ht) hu).2
    have hmul := mul_le_mul_of_nonneg_right hh (hf0 t ht)
    dsimp [Z] at hmul
    rw [show u / (2 * X) = (1 / 2) * (u / X) by ring]
    nlinarith

/-- LEAF. Unit U-1531. For `0 <= u <= 10^-4`, `e^u - 1 <= 1.00006 u`; end of the proof of
Lemma 5, p. 17. -/
theorem exp_sub_one_le_lemma5 {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 0.0001) :
    Real.exp u - 1 ≤ 1.00006 * u := by
  have h := Real.exp_bound' hu0 (show u ≤ 1 by linarith) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hu2 : u ^ 2 ≤ 0.0001 * u := by nlinarith
  have hu3 : u ^ 3 ≤ 0.00000001 * u := by
    have h1 := mul_le_mul_of_nonneg_right hu2 hu0
    have h2 := mul_le_mul_of_nonneg_left hu2 (by norm_num : (0 : ℝ) ≤ 0.0001)
    nlinarith
  nlinarith

/-- LEAF. Unit U-1531. For `0 < u <= 10^-4`, `u - log(e^u - 1) <= -1.00005 log u`; end of
the proof of Lemma 5, p. 17. -/
theorem sub_log_le_lemma5 {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.0001) :
    u - Real.log (Real.exp u - 1) ≤ -1.00005 * Real.log u := by
  have hlog : Real.log u ≤ -2 := by
    calc
      Real.log u ≤ Real.log (1 / (2 : ℝ) ^ 4) := Real.log_le_log hu0 (by norm_num; linarith)
      _ = -4 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, Real.log_pow]
        ring
      _ ≤ -2 := by linarith [Real.log_two_gt_d9]
  have he : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have hl := Real.log_le_log hu0 he
  nlinarith

/-- LEAF. Unit U-1531. For `0 < u <= 10^-4`, `10^12 <= X <= Y` and `u X > 1`, the ratio
`(u + log Y)/(log(e^u - 1) + log Y)` is at most the same ratio with `X`, since it decreases in
the logarithm; the third line of the proof of Lemma 5, p. 16. The hypothesis `u X > 1` keeps
both denominators positive, as in Theorem 4 where `u √Y >= alpha2 >= 1`. -/
theorem lemma5_ratio_mono {u X Y : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.0001) (hX : 10 ^ 12 ≤ X)
    (hXY : X ≤ Y) (huX : 1 < u * X) :
    (u + Real.log Y) / (Real.log (Real.exp u - 1) + Real.log Y) ≤
      (u + Real.log X) / (Real.log (Real.exp u - 1) + Real.log X) := by
  set C := Real.log (Real.exp u - 1)
  have h_exp_u_sub_1_pos : 0 < Real.exp u - 1 := by
    have : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu0
    linarith
  have h_Cu : C < u := by
    have : Real.exp u - 1 < Real.exp u := by linarith
    calc C = Real.log (Real.exp u - 1) := rfl
      _ < Real.log (Real.exp u) := Real.log_lt_log h_exp_u_sub_1_pos this
      _ = u := Real.log_exp u
  have hX_pos : 0 < X := by linarith
  have hY_pos : 0 < Y := by linarith
  have h_log_mono : Real.log X ≤ Real.log Y := Real.log_le_log hX_pos hXY
  have h_den_X : 0 < C + Real.log X := by
    have h_ge : Real.exp u - 1 ≥ u := by
      have : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
      linarith
    have : Real.log u ≤ C := Real.log_le_log hu0 h_ge
    have h_log_uX : 0 < Real.log (u * X) := by
      calc (0 : ℝ) = Real.log 1 := Real.log_one.symm
        _ < Real.log (u * X) := Real.log_lt_log (by norm_num) huX
    have h_log_u_plus_log_X : Real.log (u * X) = Real.log u + Real.log X := by
      rw [Real.log_mul hu0.ne' hX_pos.ne']
    linarith
  have h_den_Y : 0 < C + Real.log Y := by linarith
  have h_cross : (u + Real.log Y) * (C + Real.log X) ≤ (u + Real.log X) * (C + Real.log Y) := by
    have : (u + Real.log Y) * (C + Real.log X) - (u + Real.log X) * (C + Real.log Y) = (C - u) * (Real.log Y - Real.log X) := by ring
    have h_le_zero : (C - u) * (Real.log Y - Real.log X) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · linarith
    linarith
  rw [div_le_div_iff₀ h_den_Y h_den_X]
  exact h_cross

/-- LEAF. Unit U-1531. With `delta = m u`, `m >= 2`, `0 < u`, `m u <= 10^-4`, `a` in `[0, 1/2]`
and `Y = e^u X (1 + delta (1 - a))` for `X > 0`, one has `X >= 0.999 Y`; first line of the
proof of Theorem 4, p. 18. -/
theorem X_ge_of_Y {m : ℕ} (hm : 2 ≤ m) {u a X : ℝ} (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hX : 0 < X) :
    0.999 * (Real.exp u * X * (1 + m * u * (1 - a))) ≤ X := by
  have h_u_pos : 0 ≤ u := hu.le
  have hm_le : (m : ℝ) ≥ 2 := by exact_mod_cast hm
  have h_m_pos : 0 ≤ (m : ℝ) := by linarith
  have h_mu_nonneg : 0 ≤ (m : ℝ) * u := mul_nonneg h_m_pos h_u_pos
  have hu_le : u ≤ 0.0001 := by
    have : 2 * u ≤ (m : ℝ) * u := by
      apply mul_le_mul_of_nonneg_right
      · exact hm_le
      · exact h_u_pos
    linarith
  have h_exp : Real.exp u ≤ 1.00011 := by
    have hu_abs : |u| ≤ 1 := by
      rw [abs_of_nonneg h_u_pos]
      linarith
    have h_bound := Real.exp_bound hu_abs (n := 2) (by norm_num)
    have h_sum : ∑ k ∈ Finset.range 2, u ^ k / ↑k.factorial = 1 + u := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    rw [h_sum] at h_bound
    have h_abs_u : |u| = u := abs_of_nonneg h_u_pos
    rw [h_abs_u] at h_bound
    have h_rhs : u ^ 2 * (↑(Nat.succ 2) / (↑(Nat.factorial 2) * (2 : ℝ))) = u ^ 2 * (3 / 4) := by
      norm_num
    have h_bound2 : |Real.exp u - (1 + u)| ≤ u ^ 2 * (3 / 4) := by
      calc |Real.exp u - (1 + u)| ≤ u ^ 2 * (↑(Nat.succ 2) / (↑(Nat.factorial 2) * (2 : ℝ))) := h_bound
        _ = u ^ 2 * (3 / 4) := h_rhs
    have h_le : Real.exp u - (1 + u) ≤ u ^ 2 * (3 / 4) := le_trans (le_abs_self _) h_bound2
    have h_u2 : u ^ 2 ≤ 0.0001 * u := by
      calc u ^ 2 = u * u := by ring
        _ ≤ 0.0001 * u := mul_le_mul_of_nonneg_right hu_le h_u_pos
    calc Real.exp u = Real.exp u - (1 + u) + (1 + u) := by ring
      _ ≤ u ^ 2 * (3 / 4) + (1 + u) := by linarith
      _ ≤ (0.0001 * u) * (3 / 4) + 1 + u := by
        have : u ^ 2 * (3 / 4) ≤ (0.0001 * u) * (3 / 4) := mul_le_mul_of_nonneg_right h_u2 (by norm_num)
        linarith
      _ = 1 + 1.000075 * u := by ring
      _ ≤ 1 + 1.000075 * 0.0001 := by
        have : 1.000075 * u ≤ 1.000075 * 0.0001 := mul_le_mul_of_nonneg_left hu_le (by norm_num)
        linarith
      _ ≤ 1.00011 := by norm_num
  have h_factor : 1 + (m : ℝ) * u * (1 - a) ≤ 1.0001 := by
    have h_a : 1 - a ≤ 1 := by linarith
    have h_mu : (m : ℝ) * u * (1 - a) ≤ 0.0001 * 1 := by
      apply mul_le_mul hmu h_a
      · linarith
      · exact (by norm_num)
    linarith
  have h_factor_pos : 0 ≤ 1 + (m : ℝ) * u * (1 - a) := by
    have : 0 ≤ (m : ℝ) * u * (1 - a) := by
      apply mul_nonneg
      · exact h_mu_nonneg
      · linarith
    linarith
  have h_prod : 0.999 * Real.exp u * (1 + (m : ℝ) * u * (1 - a)) ≤ 1 := by
    calc 0.999 * Real.exp u * (1 + (m : ℝ) * u * (1 - a))
      _ ≤ 0.999 * 1.00011 * (1 + (m : ℝ) * u * (1 - a)) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left h_exp (by norm_num)
        · exact h_factor_pos
      _ ≤ 0.999 * 1.00011 * 1.0001 := by
        apply mul_le_mul_of_nonneg_left h_factor (by norm_num)
      _ ≤ 1 := by norm_num
  calc 0.999 * (Real.exp u * X * (1 + m * u * (1 - a))) = (0.999 * Real.exp u * (1 + m * u * (1 - a))) * X := by ring
    _ ≤ 1 * X := mul_le_mul_of_nonneg_right h_prod hX.le
    _ = X := by ring

/-- LEAF. Unit U-1531. The Riemann zeta function has no zero on the real segment `]0, 1[`, so
every nontrivial zero has nonzero ordinate, as the split by `|gamma|` on p. 19 and Lemma 2 on
p. 14 use. -/
theorem riemannZeta_ne_zero_of_real {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    riemannZeta (s : ℂ) ≠ 0 := by
  have hf (r : ℝ) (hrhalf : 1 / 2 ≤ r) (hr1 : r < 1) : riemannZeta (r : ℂ) ≠ 0 := by
    have hrpos : 0 < r := by linarith
    have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
    have hrone : (r : ℂ) ≠ 1 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at hh
      linarith
    intro hz
    let I : ℂ := ∫ x in Set.Ioi (1 : ℝ),
      (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((r : ℂ) + 1)
    have he := Zeta0EqZeta (N := 1) (by norm_num) (s := (r : ℂ))
      (by simpa using hrpos) hrone
    rw [hz] at he
    norm_num [riemannZeta0, Finset.sum_range_succ, Complex.zero_cpow hrne] at he
    change (1 : ℂ) + -1 / (1 - (r : ℂ)) + -(1 / 2) + (r : ℂ) * I = 0 at he
    have hid : 1 / (1 - (r : ℂ)) = (1 / 2 : ℂ) + (r : ℂ) * I := by
      linear_combination -he
    have hb := ZetaBnd_aux1b 1 (by norm_num) (σ := r) (t := 0) hrpos
    simp only [Nat.cast_one, Complex.ofReal_zero, zero_mul, add_zero, Real.one_rpow] at hb
    change ‖I‖ ≤ 1 / r at hb
    have hm : r * ‖I‖ ≤ 1 := by
      have hh := (le_div_iff₀ hrpos).mp hb
      nlinarith
    have hn : ‖(1 : ℂ) / (1 - (r : ℂ))‖ ≤ 1 / 2 + r * ‖I‖ := by
      rw [hid]
      calc
        ‖(1 / 2 : ℂ) + (r : ℂ) * I‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(r : ℂ) * I‖ := norm_add_le _ _
        _ = 1 / 2 + r * ‖I‖ := by
          rw [norm_mul]
          norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    have hn' : (1 : ℝ) / (1 - r) ≤ 1 / 2 + r * ‖I‖ := by
      simpa only [norm_div, norm_one, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1)] using hn
    have htwo : (2 : ℝ) ≤ 1 / (1 - r) := by
      rw [le_div_iff₀ (sub_pos.mpr hr1)]
      linarith
    linarith
  by_cases hs : 1 / 2 ≤ s
  · exact hf s hs h1
  · intro hz
    have hh := LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero
      (ρ := (s : ℂ)) (by simpa using h0) (by simpa using h1) hz
    exact hf (1 - s) (by linarith) (by linarith) (by simpa using hh)

/-! ### Assemblies -/

lemma fm_nonneg' (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ fm m t := by
  unfold fm
  have : 0 ≤ 4 * t * (1 - t) := by nlinarith [ht.1, ht.2]
  positivity

lemma integral_fm_pos (m : ℕ) : 0 < ∫ t in (0 : ℝ)..1, fm m t := by
  rw [norm_fm]; positivity

/-- **Display (15), p. 20, from the split of `J`.** Let `m >= 2`, `X >= 10^12`, `u > 0`,
`m u <= 10^-4`, `delta = m u`. Suppose the `psi` integral against `f_m` equals the main term
minus the zero terms with `|gamma| <= T`, at most `2N(T) u (1 + delta) √X ||f_m||_1` in total,
minus the zero terms with `|gamma| > T`, at most
`(e^u + 1)(1 + delta)^(m+1) mu*_m ||f_m||_1 / delta^m` times `Zs`, the sum of
`X^beta/|gamma|^(m+1)`, minus the log term. Then the multiplied out display (15) of
`JLower15Lit` holds. PROVED CONDITIONAL ON the leaves `main_term_ge` and
`log_term_integral_le`. -/
theorem display15_of_split {m : ℕ} (hm : 2 ≤ m) {X u NT Zs Near Far : ℝ} (hX : 10 ^ 12 ≤ X)
    (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    (hJ : (∫ t in (0 : ℝ)..1,
        (ψ (X * Real.exp u * (1 + m * u * t)) - ψ (X * (1 + m * u * t))) * fm m t) =
      (∫ t in (0 : ℝ)..1,
          (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) - Near - Far -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t)
    (hNear : Near ≤ 2 * NT * (u * (1 + m * u) * √X * ∫ t in (0 : ℝ)..1, fm m t))
    (hFar : Far ≤ (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m *
        (∫ t in (0 : ℝ)..1, fm m t) / (m * u) ^ m * Zs) :
    u * X * (1 - 1 / X ^ 2 - (1 + m * u) * (2 * NT) / √X -
        (1 + m * u) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * (m * u) ^ m)) *
          (Zs / X)) * (∫ t in (0 : ℝ)..1, fm m t) ≤
      ∫ t in (0 : ℝ)..1,
        (ψ (X * Real.exp u * (1 + m * u * t)) - ψ (X * (1 + m * u * t))) * fm m t := by
  have hX0 : 0 < X := by linarith
  have hδ : 0 ≤ (m : ℝ) * u := by positivity
  have hF := integral_fm_pos m
  have hmain := main_term_ge (f := fm m) (continuous_fm m).continuousOn
    (fun t ht => fm_nonneg' m ht) hu.le hδ hX0.le
  have hlog := log_term_integral_le (f := fm m) (continuous_fm m).continuousOn
    (fun t ht => fm_nonneg' m ht) hX hu.le hδ
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX0
  have hss : √X * √X = X := Real.mul_self_sqrt hX0.le
  have hmu0 : 0 < (m : ℝ) * u := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hpow : 0 < ((m : ℝ) * u) ^ m := pow_pos hmu0 m
  set F := ∫ t in (0 : ℝ)..1, fm m t
  have key : u * X * (1 - 1 / X ^ 2 - (1 + m * u) * (2 * NT) / √X -
        (1 + m * u) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * (m * u) ^ m)) *
          (Zs / X)) * F =
      u * X * F - u * F / X - 2 * NT * (u * (1 + m * u) * √X * F) -
        (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m * F / (m * u) ^ m * Zs := by
    have gen : ∀ s : ℝ, 0 < s → s * s = X →
        u * (s * s) * (1 - 1 / (s * s) ^ 2 - (1 + m * u) * (2 * NT) / s -
          (1 + m * u) ^ (m + 1) * muStar m * ((Real.exp u + 1) / (u * (m * u) ^ m)) *
            (Zs / (s * s))) * F =
        u * (s * s) * F - u * F / (s * s) - 2 * NT * (u * (1 + m * u) * s * F) -
          (Real.exp u + 1) * (1 + m * u) ^ (m + 1) * muStar m * F / (m * u) ^ m * Zs := by
      intro s hs _
      field_simp
    have := gen (√X) hsX hss
    rw [hss] at this
    exact this
  rw [key, hJ]
  have h2 : u / (2 * X) * F ≤ u * F / X := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hX0]
    nlinarith [mul_pos hu hF]
  linarith

/-- **The `alpha1` step from (15) to (16), p. 20.** If `2N(T) <= alpha1 √Y`, `alpha1 >= 0` and
`Y = e^u X (1 + delta (1 - a))` with the hypotheses of `X_ge_of_Y`, then
`2N(T)/√X <= alpha1/√0.999`. PROVED CONDITIONAL ON the leaf `X_ge_of_Y`. -/
theorem near_term_alpha1 {m : ℕ} (hm : 2 ≤ m) {u a X NT α1 : ℝ} (hu : 0 < u)
    (hmu : (m : ℝ) * u ≤ 0.0001) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hX : 0 < X) (hα1 : 0 ≤ α1)
    (hN : 2 * NT ≤ α1 * √(Real.exp u * X * (1 + m * u * (1 - a)))) :
    2 * NT / √X ≤ α1 / √0.999 := by
  have hY := X_ge_of_Y hm hu hmu ha0 ha1 hX
  set Y := Real.exp u * X * (1 + m * u * (1 - a))
  have hsX : 0 < √X := Real.sqrt_pos.mpr hX
  have h999 : 0 < √(0.999 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsY : √(0.999 : ℝ) * √Y ≤ √X := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hY
  rw [div_le_div_iff₀ hsX h999]
  calc 2 * NT * √0.999 ≤ α1 * √Y * √0.999 := mul_le_mul_of_nonneg_right hN h999.le
    _ = α1 * (√0.999 * √Y) := by ring
    _ ≤ α1 * √X := mul_le_mul_of_nonneg_left hsY hα1

end LeanLab.RamareSaouter2003.Decomp1531b
