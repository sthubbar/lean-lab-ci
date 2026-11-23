/-
P0069 Baker Harman Pintz 1997, page 22, Lemma 8 with epsilon equal to the reciprocal
of log x, as used on the horizontal sides of the Perron rectangle before display 3.36.
Rademacher reference 28, pages 195, 197, 198 and 199, with every constant explicit.

This file proves the statement of
`LeanLab.BHP1997.DecompC165a.Contour230.horizontal_convexity_input`, copied verbatim, as
`horizontal_convexity_input_s64`. It is CONDITIONAL ON exactly one open input, the leaf
`LeanLab.BHP1997.Decomp530a.leaf_regularPart_finite_order_growth`, which is already on
the route of `AssemblyC165.theorem1` through `rademacher_convexity`. So the separate
named input `horizontal_convexity_input` is no longer needed.

The proof takes delta equal to 1 / (log x + 4). The Gamma quotient constant is one by
the PROVED `leaf_rademacher_gamma_ratio`, the left edge then costs 1 + 1 / delta, the
right edge costs 1 + 2 / delta, and the Gaussian localized three lines interpolation
costs the absolute factor 3 e^4. All three are uniform in delta, which is why the
interpolation step is restated here with its constant explicit: the existing
`weighted_strip_interpolation_finite_order` hides its constant behind an existential
quantifier that may depend on delta. Right of the line 1 + delta the Euler product bound
suffices. The pole term is at most 4 because the height is at least 1 / 4.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp530a

namespace LeanLab.BHP1997.DecompC165a.Contour230
open Classical Complex Set Filter
open LeanLab.BHP1997.Decomp530a

/-- Rademacher page 195 display 3.4, weighted three lines interpolation on the closed strip
from minus delta to one plus delta, with the absolute constant 3 e^4 made explicit.
The proof is the Gaussian localization proof of
`Decomp530a.weighted_strip_interpolation_finite_order`, whose statement only asserts some
constant. CONDITIONAL ON the finite order growth and boundary premises, all hypotheses. -/
theorem weighted_strip_interpolation_explicit_s64 {δ : ℝ} (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (Q A : ℝ) (hQ : 1 ≤ Q) (hA : 0 < A)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s : ℂ,
        -δ ≤ s.re → s.re ≤ 1 + δ → ‖f s‖ ≤ C * Real.exp (|s.im| ^ c))
    (hleft : ∀ t : ℝ, ‖f (((-δ : ℝ) : ℂ) + t * I)‖ ≤
        A * (Q * (|t| + 2)) ^ (1 / 2 + δ))
    (hright : ∀ t : ℝ, ‖f (((1 + δ : ℝ) : ℂ) + t * I)‖ ≤ A)
    (σ t : ℝ) (hσ0 : -δ ≤ σ) (hσ1 : σ ≤ 1 + δ) :
    ‖f ((σ : ℂ) + t * I)‖ ≤
      3 * Real.exp 4 * A * (Q * (|t| + 1)) ^ ((1 + δ - σ) / 2) := by
  obtain ⟨C, c, hC, hc, hg⟩ := hg
  let K : ℝ := 3 * Real.exp 4
  let P : ℝ := Q * (|t| + 1)
  let a : ℝ := 1 / 2 + δ
  let g : ℂ → ℂ := fun z => f (z + t * I) * Complex.exp ((z - σ) ^ 2)
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have h4 (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) : (z.re - σ) ^ 2 ≤ 4 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 2 - (z.re - σ))
      (by linarith : 0 ≤ 2 + (z.re - σ))
    nlinarith
  have hdamp (z : ℂ) (hz : -δ ≤ z.re ∧ z.re ≤ 1 + δ) :
      (|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) ≤ K := by
    calc
      _ ≤ (|z.im| + 2) * Real.exp (4 - z.im ^ 2) := by
        gcongr
        exact h4 z hz
      _ = Real.exp 4 * ((|z.im| + 2) * Real.exp (-(z.im ^ 2))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ Real.exp 4 * 3 := mul_le_mul_of_nonneg_left (gaussian_linear_decay z.im) (Real.exp_pos _).le
      _ = K := by dsimp [K]; ring
  have hgl (z : ℂ) (hz : z.re = -δ) : ‖g z‖ ≤ K * A * P ^ a := by
    have he : z + t * I = (((-δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hl := hleft (z.im + t)
    have hheight : |z.im + t| + 2 ≤ (|t| + 1) * (|z.im| + 2) := by
      have hh := abs_add_le z.im t
      nlinarith [abs_nonneg z.im, abs_nonneg t]
    have hp : (Q * (|z.im + t| + 2)) ^ a ≤ P ^ a * (|z.im| + 2) := by
      calc
        _ ≤ (P * (|z.im| + 2)) ^ a := by
          apply Real.rpow_le_rpow (by positivity) _ ha
          dsimp [P]
          nlinarith
        _ = P ^ a * (|z.im| + 2) ^ a := Real.mul_rpow hP.le (by positivity)
        _ ≤ P ^ a * (|z.im| + 2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le (by linarith [abs_nonneg z.im]) ha1)
            (Real.rpow_nonneg hP.le _)
    have hn : ‖f (z + t * I)‖ ≤ (A * P ^ a) * (|z.im| + 2) := by
      rw [he]
      calc
        _ ≤ A * (P ^ a * (|z.im| + 2)) := hl.trans (mul_le_mul_of_nonneg_left hp hA.le)
        _ = _ := by ring
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ ((A * P ^ a) * (|z.im| + 2)) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = (A * P ^ a) * ((|z.im| + 2) * Real.exp ((z.re - σ) ^ 2 - z.im ^ 2)) := by ring
      _ ≤ (A * P ^ a) * K := mul_le_mul_of_nonneg_left
        (hdamp z (by constructor <;> rw [hz] <;> linarith)) (by positivity)
      _ = _ := by ring
  have hgr (z : ℂ) (hz : z.re = 1 + δ) : ‖g z‖ ≤ K * A := by
    have he : z + t * I = (((1 + δ : ℝ) : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp [hz]
    have hr : ‖f (z + t * I)‖ ≤ A := by rw [he]; exact hright (z.im + t)
    have hr4 := h4 z (by constructor <;> rw [hz] <;> linarith)
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ A * Real.exp 4 := mul_le_mul hr (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z.im]))
        (Real.exp_pos _).le hA.le
      _ ≤ K * A := by dsimp [K]; nlinarith [Real.exp_pos 4]
  have hgd : Differentiable ℂ g := by
    dsimp [g]
    exact (hf.comp (by fun_prop)).mul (by fun_prop)
  have hgg (z : ℂ) (hzl : -δ ≤ z.re) (hzu : z.re ≤ 1 + δ) :
      ‖g z‖ ≤ (C * Real.exp 4) * Real.exp (|z.im + t| ^ c) := by
    have hh := hg (z + t * I) (by simpa using hzl) (by simpa using hzu)
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at hh
    change ‖f (z + t * I) * Complex.exp ((z - σ) ^ 2)‖ ≤ _
    rw [localized_norm]
    calc
      _ ≤ (C * Real.exp (|z.im + t| ^ c)) * Real.exp 4 :=
        mul_le_mul hh (Real.exp_le_exp.mpr (by nlinarith [h4 z ⟨hzl, hzu⟩, sq_nonneg z.im]))
          (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hi := finite_order_three_lines (l := -δ) (u := 1 + δ) (a := K * A * P ^ a)
    (b := K * A) (C := C * Real.exp 4) (c := c) (t₀ := t)
    (by linarith) (by positivity) (by positivity) (by positivity) hc g hgd hgg hgl hgr
    (z := (σ : ℂ)) (by simpa using hσ0) (by simpa using hσ1)
  simp only [g, sub_self, zero_pow (by norm_num : 2 ≠ 0), Complex.exp_zero, mul_one,
    ofReal_re, sub_neg_eq_add] at hi
  let w : ℝ := (σ + δ) / (1 + 2 * δ)
  have hden : 1 + δ + δ = 1 + 2 * δ := by ring
  rw [hden] at hi
  change ‖f ((σ : ℂ) + t * I)‖ ≤ (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w at hi
  have hex : a * (1 - w) = (1 + δ - σ) / 2 := by
    dsimp [a, w]
    field_simp [show 1 + 2 * δ ≠ 0 by linarith]
    ring
  have hKA : 0 < K * A := mul_pos hK hA
  have halg : (K * A * P ^ a) ^ (1 - w) * (K * A) ^ w =
      K * A * P ^ ((1 + δ - σ) / 2) := by
    rw [Real.mul_rpow hKA.le (Real.rpow_nonneg hP.le a), ← Real.rpow_mul hP.le, hex]
    calc
      _ = ((K * A) ^ (1 - w) * (K * A) ^ w) * P ^ ((1 + δ - σ) / 2) := by ring
      _ = _ := by rw [← Real.rpow_add hKA, sub_add_cancel, Real.rpow_one]
  exact hi.trans_eq halg

/-- Rademacher pages 197 to 199, display 6.2, for the pole subtracted L-function: on the
line minus delta its norm is at most 6 + 6 / delta times the weight
(q (|u| + 2))^(1/2 + delta), with no other dependence on delta, q or the character. The
Gamma quotient constant is one by the PROVED `leaf_rademacher_gamma_ratio`. PROVED. -/
theorem regularPart_left_bound_s64 {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ‖regularPart χ (((-δ : ℝ) : ℂ) + u * I)‖ ≤
      (6 + 6 / δ) * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) := by
  have hgamma : ∀ (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d)
      (s : ℂ), s.re = -δ →
      ‖ψ⁻¹.gammaFactor (1 - s) / ψ.gammaFactor s‖ ≤
        1 * (|s.im| + 2) ^ (1 / 2 + δ) := by
    intro d _ ψ s hs
    simpa only [one_mul] using
      gamma_quotient_normalization hδ hδhalf leaf_rademacher_gamma_ratio ψ s hs
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let s : ℂ := ((-δ : ℝ) : ℂ) + u * I
  have hsre : s.re = -δ := by simp [s]
  have hs : s ≠ 1 := by
    intro he; have := congrArg Complex.re he; simp only [hsre, one_re] at this; linarith
  have hd : 1 ≤ ‖s - 1‖ := by
    have hh := Complex.abs_re_le_norm (s - 1)
    simp only [sub_re, one_re, hsre, abs_of_nonpos (by linarith : -δ - 1 ≤ 0)] at hh
    linarith
  have hp : 1 / ‖s - 1‖ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd
  have hbase : 1 ≤ (q : ℝ) * (|u| + 2) := by nlinarith [abs_nonneg u]
  have hpow : 1 ≤ ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) :=
    Real.one_le_rpow hbase (by linarith)
  have hl := all_character_left_bound hδ zero_le_one hgamma χ u
  have hr := (pole_norm_bounds χ hs).1
  change ‖regularPart χ s‖ ≤ _
  change ‖χ.LFunction s‖ ≤ (4 * 1 * (1 + 1 / δ)) * ((q : ℝ) * (|u| + 2)) ^ (1 / 2 + δ) at hl
  have hBA : 4 * 1 * (1 + 1 / δ) + 1 ≤ 6 + 6 / δ := by
    have hd0 : 0 < 1 / δ := by positivity
    have : 6 / δ = 6 * (1 / δ) := by ring
    rw [this]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hBA
    (Real.rpow_nonneg (by positivity : 0 ≤ (q : ℝ) * (|u| + 2)) (1 / 2 + δ))
  nlinarith

/-- The statement of `horizontal_convexity_input` in Decomp488c, copied verbatim.
P0069 page 22, Lemma 8 at epsilon equal to 1 / log x, as used in the horizontal display
before 3.36. Proof with delta equal to 1 / (log x + 4): left of the line 1 + delta the
explicit interpolation applied to the pole subtracted L-function gives
3 e^4 (12 + 6 log x + 24) (q (|tau| + 1))^((1 + delta - Re s) / 2), and that exponent is
at most 1 / 2 + 1 / log x - sigma; the pole term is at most 4. Right of that line the
Euler product gives 1 + 1 / delta = 5 + log x. CONDITIONAL ON
`Decomp530a.leaf_regularPart_finite_order_growth` only; the sealed theorem
`horizontal_convexity_input` is not used. -/
theorem horizontal_convexity_input_s64 :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x →
        1 / 4 ≤ |τ| → |τ| ≤ 2 * x →
        ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
          C * Real.log x *
            (((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) + 1) := by
  refine ⟨3 * Real.exp 4 * 66 + 11, by positivity, ?_⟩
  intro x hx q _ hq hqx χ σ τ hσ0 hσc hτ hτx
  set L : ℝ := Real.log x with hLdef
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
  have hLh : (1 : ℝ) / 2 ≤ L := by linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  set δ : ℝ := 1 / (L + 4) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδinv : 1 / δ = L + 4 := by rw [hδdef, one_div_one_div]
  have hδL : δ ≤ 1 / L := by
    rw [hδdef]; exact one_div_le_one_div_of_le hL0 (by linarith)
  have hδhalf : δ < 1 / 2 := by
    rw [hδdef, div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set r : ℝ := 1 / 2 + σ with hrdef
  set s : ℂ := ((r : ℝ) : ℂ) + τ * I with hsdef
  have hsre : s.re = r := by simp [hsdef]
  have hsim : s.im = τ := by simp [hsdef]
  set P : ℝ := (q : ℝ) * (|τ| + 1) with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; nlinarith [abs_nonneg τ]
  set e : ℝ := 1 / 2 + 1 / L - σ with hedef
  have hPe : 0 ≤ P ^ e := Real.rpow_nonneg (by linarith) _
  set D : ℝ := 3 * Real.exp 4 * 66 + 11 with hDdef
  have hE : 0 < 3 * Real.exp 4 := by positivity
  have hRHS : D * L * 1 ≤ D * L * (P ^ e + 1) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  change ‖χ.LFunction s‖ ≤ D * L * (P ^ e + 1)
  rcases le_or_gt r (1 + δ) with hr | hr
  · -- left of the line 1 + delta: interpolation of the regular part, plus the pole
    have hA : 0 < 6 + 6 / δ := by positivity
    have hi := weighted_strip_interpolation_explicit_s64 hδ hδhalf (q : ℝ) (6 + 6 / δ) hqR hA
      (regularPart χ) (regularPart_entire χ)
      (leaf_regularPart_finite_order_growth hδ hδhalf χ)
      (regularPart_left_bound_s64 hδ hδhalf χ)
      (fun u => (regularPart_right_bound hδ χ u).trans (by
        have : 2 / δ ≤ 6 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
        linarith))
      r τ (by rw [hrdef]; linarith) hr
    have hexp : (1 + δ - r) / 2 ≤ e := by rw [hedef, hrdef] at *; linarith
    have hpow : P ^ ((1 + δ - r) / 2) ≤ P ^ e := Real.rpow_le_rpow_of_exponent_le hP1 hexp
    have hreg : ‖regularPart χ s‖ ≤ 3 * Real.exp 4 * (6 + 6 / δ) * P ^ e := by
      rw [hsdef]
      exact hi.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    have hs1 : s ≠ 1 := by
      intro h; have := congrArg Complex.im h; rw [hsim, one_im] at this
      rw [this, abs_zero] at hτ; linarith
    have hd : |τ| ≤ ‖s - 1‖ := by
      have hh := Complex.abs_im_le_norm (s - 1)
      simpa [hsim] using hh
    have hpole : 1 / ‖s - 1‖ ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hLf := (pole_norm_bounds χ hs1).2
    have hA66 : 6 + 6 / δ ≤ 66 * L := by
      have : 6 / δ = 6 * (1 / δ) := by ring
      rw [this, hδinv]; linarith
    have hmain : 3 * Real.exp 4 * (6 + 6 / δ) * P ^ e ≤ 3 * Real.exp 4 * 66 * L * P ^ e := by
      have := mul_le_mul_of_nonneg_left hA66 hE.le
      have := mul_le_mul_of_nonneg_right this hPe
      linarith
    have h4L : (4 : ℝ) ≤ 11 * L := by linarith
    have hfin : D * L * (P ^ e + 1) =
        3 * Real.exp 4 * 66 * L * P ^ e + 3 * Real.exp 4 * 66 * L + 11 * L * P ^ e + 11 * L := by
      rw [hDdef]; ring
    have hpos1 : 0 ≤ 3 * Real.exp 4 * 66 * L := by positivity
    have hpos2 : 0 ≤ 11 * L * P ^ e := by positivity
    linarith
  · -- right of the line 1 + delta: the Euler product bound
    have hr1 : 1 < s.re := by rw [hsre]; linarith
    have hb := Repair499Euler.LFunction_norm_le χ hr1
    rw [hsre] at hb
    have hrd : 1 / (r - 1) ≤ 1 / δ := one_div_le_one_div_of_le hδ (by linarith)
    have h11 : 1 + 1 / δ ≤ D * L * 1 := by
      rw [hδinv, hDdef]
      have : 0 ≤ 3 * Real.exp 4 * 66 * L := by positivity
      nlinarith
    linarith

end LeanLab.BHP1997.DecompC165a.Contour230

#print axioms LeanLab.BHP1997.DecompC165a.Contour230.horizontal_convexity_input_s64
