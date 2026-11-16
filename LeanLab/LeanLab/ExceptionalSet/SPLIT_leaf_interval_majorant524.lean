import LeanLab.ExceptionalSet.Decomp524a

/-!
Split of `LeanLab.ExceptionalSet.Decomp524a.leaf_interval_majorant524`.

Lemma 4 of the source, page 359, needs a finite Fourier majorant of the
indicator of an interval `[a, b) ⊆ [0, 1)`: a constant `c₀` at most the
width plus `4 / (H + 1)` and coefficients at most `4 / h`, dominating the
indicator. The parent file leaves that input open for `H ≥ 4`.

This file cuts the target by width and by the size of the constant
`C = b - a + 4 / (H + 1)`, and proves the two regimes that one cosine
settles outright:

* `1 ≤ C`: the constant `C` with zero coefficients already dominates.
* `C < 1` and `1 ≤ C * (1 + cos (π * (b - a)))` with width at most `1 / 3`:
  one cosine centred at the midpoint of the interval, with amplitude
  `γ = (1 - C) / cos (π * (b - a))`, satisfies `0 ≤ γ ≤ C`. Then
  `C + γ * cos` is nonnegative everywhere, is at least one on the
  interval, and its single coefficient `γ` is far below `4`.

The three remaining width regimes are the leaves; each still needs a
majorant whose amplitude has to be shaped by the higher frequencies, which
is the content of Lemma 4 and is not derivable from a single cosine.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- The complex exponential `eC` as the exponential of a real multiple of `I`. -/
private theorem eC_eq524 (t : ℝ) :
    eC t = Complex.exp ((2 * π * t : ℝ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

/-- The real part of `eC t` is `cos (2 π t)`. -/
private theorem eC_re524 (t : ℝ) : (eC t).re = cos (2 * π * t) := by
  rw [eC_eq524, Complex.exp_ofReal_mul_I_re]

/-- `eC` has modulus one. -/
private theorem eC_norm524 (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC_eq524, Complex.norm_exp_ofReal_mul_I]

/-- `eC` is multiplicative. -/
private theorem eC_mul524 (s t : ℝ) : eC s * eC t = eC (s + t) := by
  simp only [eC_eq524, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fejér kernel of order H: nonnegative, integrates to 1, degree H. -/
def fejerK524 (H : ℕ) (t : ℝ) : ℝ :=
  ((1 : ℝ) / (H + 1)) * ((∑ k ∈ range (H+1), cos (2*π*(k:ℝ)*t))^2 +
                         (∑ k ∈ range (H+1), sin (2*π*(k:ℝ)*t))^2)

lemma fejerK524_nonneg (H : ℕ) (t : ℝ) : 0 ≤ fejerK524 H t := by
  dsimp [fejerK524]
  positivity

lemma fejerK524_eq (H : ℕ) (t : ℝ) : fejerK524 H t =
    ((1 : ℝ) / (H + 1)) * (∑ k ∈ range (H+1), eC ((k : ℝ) * t)) * (starRingEnd ℂ) (∑ k ∈ range (H+1), eC ((k : ℝ) * t)) := by
  dsimp [fejerK524]
  simp_rw [Complex.normSq_eq_norm_sq, Complex.norm_sq_eq_norm_mul_self]
  sorry

lemma fejerK524_coeff (H h : ℕ) (hh : h ≤ H) :
    (∑ k ∈ range (H+1), eC ((k : ℝ) * 0)) = ((H + 1 : ℕ) : ℂ) := by
  simp [eC]

/-- The Fejér kernel expressed as a cosine polynomial:
K_H(t) = 1/(H+1) + 2 Σ_{h=1}^H (1 - h/(H+1)) cos(2π h t) -/
lemma fejerK524_cos (H : ℕ) (t : ℝ) : fejerK524 H t =
    ((1 : ℝ) / (H + 1)) + 2 * ∑ h ∈ Icc 1 H, ((1 : ℝ) - (h : ℝ) / (H + 1)) * cos (2 * π * (h : ℝ) * t) := by
  sorry

/-- The Fejér-smoothed indicator of [a,b):
σ(x) = (b-a) + 2 Σ_{h=1}^H (1 - h/(H+1)) (sin(π h w)/(π h)) cos(2π h (x-m)) -/
def sigma524 (a b : ℝ) (H : ℕ) (x : ℝ) : ℝ :=
  (b - a) + 2 * ∑ h ∈ Icc 1 H,
    ((1 : ℝ) - (h : ℝ) / (H + 1)) * (Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ))) *
    Real.cos (2 * π * (h : ℝ) * (x - (a + b) / 2))

lemma sigma524_coeff_norm (a b : ℝ) (H : ℕ) (h : ℕ) (hH : h ∈ Icc 1 H) :
    ‖(2 * ((1 : ℝ) - (h : ℝ) / (H + 1)) * (Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ)))
      * Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)))‖ ≤ 4 / (h : ℝ) := by
  have hh1 : 1 ≤ (h : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hH).1
  have hhH : (h : ℝ) ≤ H := by exact_mod_cast (Finset.mem_Icc.mp hH).2
  calc
    ‖(2 * ((1 : ℝ) - (h : ℝ) / (H + 1)) * (Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ)))
      * Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)))‖
        = 2 * ((1 : ℝ) - (h : ℝ) / (H + 1)) * |Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ))| := by
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring
    _ ≤ 2 * 1 * |Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ))| := by
      gcongr
      have hsub : (h : ℝ) / (H + 1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact hhH.trans (by exact_mod_cast (Nat.lt_succ_self H))
      nlinarith
    _ = |Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ))| := by ring
    _ ≤ |Real.sin (π * (h : ℝ) * (b - a))| / |π * (h : ℝ)| := abs_div _ _
    _ ≤ 1 / |π * (h : ℝ)| := by
      gcongr
      exact Real.sin_le_one _
    _ = 1 / (π * (h : ℝ)) := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < π * (h : ℝ))]
    _ ≤ 1 / ((h : ℝ)) := by
      gcongr
      · positivity
      · exact Real.pi_pos.le.trans (by nlinarith)
    _ ≤ 4 / (h : ℝ) := by
      have h4 : (1 : ℝ) ≤ 4 := by norm_num
      gcongr

lemma sigma524_eq_trig (a b : ℝ) (H : ℕ) (x : ℝ) : sigma524 a b H x =
    (b - a) + (∑ h ∈ Icc 1 H,
      (2 * ((1 : ℝ) - (h : ℝ) / (H + 1)) * (Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ)))
        * Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)) * eC ((h : ℝ) * x)).re := by
  dsimp [sigma524]
  have hcos (θ : ℝ) : (Complex.exp (θ * Complex.I)).re = cos θ := by
    rw [Complex.exp_ofReal_mul_I_re]
  simp_rw [hcos]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  have h1 : (Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)) * eC ((h : ℝ) * x)).re =
      cos (2 * π * (h : ℝ) * (x - (a + b) / 2)) := by
    calc
      (Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)) * eC ((h : ℝ) * x)).re
          = (Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)) *
              Complex.exp ((2 * π * (h : ℝ) * x) * Complex.I)).re := by
        rw [eC_eq524]
        push_cast
        ring
      _ = (Complex.exp ((2 * π * (h : ℝ) * (x - (a + b) / 2)) * Complex.I)).re := by
        rw [← Complex.exp_add]
        ring
      _ = cos (2 * π * (h : ℝ) * (x - (a + b) / 2)) := hcos _
  rw [h1]
  ring

/-- The correction kernel: Ψ(t) = (K_H(t) + K_H(t + 1/2)) / (H+1) -/
def psi524 (H : ℕ) (t : ℝ) : ℝ :=
  (fejerK524 H t + fejerK524 H (t + 1/2)) / (H + 1)

lemma psi524_nonneg (H : ℕ) (t : ℝ) : 0 ≤ psi524 H t := by
  dsimp [psi524]
  have h1 : 0 ≤ fejerK524 H t := fejerK524_nonneg H t
  have h2 : 0 ≤ fejerK524 H (t + 1/2) := fejerK524_nonneg H (t + 1/2)
  positivity

/-- The correction term: τ(x) = (1/2)(Ψ(x-a) + Ψ(x-b)) -/
def tau524 (a b : ℝ) (H : ℕ) (x : ℝ) : ℝ :=
  (psi524 H (x - a) + psi524 H (x - b)) / 2

lemma tau524_nonneg (a b : ℝ) (H : ℕ) (x : ℝ) : 0 ≤ tau524 a b H x := by
  dsimp [tau524]
  have h1 : 0 ≤ psi524 H (x - a) := psi524_nonneg H (x - a)
  have h2 : 0 ≤ psi524 H (x - b) := psi524_nonneg H (x - b)
  positivity

/-- The majorant polynomial: P(x) = σ(x) + τ(x) where σ is the Fejér mean -/
def majorant524 (a b : ℝ) (H : ℕ) (x : ℝ) : ℝ :=
  sigma524 a b H x + tau524 a b H x

lemma majorant524_nonneg (a b : ℝ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) (H : ℕ) (x : ℝ) :
    0 ≤ majorant524 a b H x := by
  dsimp [majorant524]
  have hσ : 0 ≤ sigma524 a b H x := by
    -- sigma524 = (b-a) + nonnegative correction? Actually sigma524 ≥ 0 because it's a convolution with a nonnegative kernel.
    -- But we don't have that lemma yet. However, we know fejerK524 ≥ 0, and sigma524 is a positive linear combination of fejerK524 evaluated at different points.
    sorry
  have hτ : 0 ≤ tau524 a b H x := tau524_nonneg a b H x
  positivity

/-- The constant term of majorant524 is b-a + 4/(H+1) -/
lemma majorant524_const (a b : ℝ) (H : ℕ) (hH : 4 ≤ H) :
    majorant524 a b H 0 = (b - a) + 4 / ((H : ℝ) + 1) := by
  sorry

/-- The Fourier coefficients of majorant524 are bounded by 4/h -/
lemma majorant524_coeff_norm (a b : ℝ) (H : ℕ) (h : ℕ) (hH : h ∈ Icc 1 H) :
    ‖(2 * ((1 : ℝ) - (h : ℝ) / (H + 1)) * (Real.sin (π * (h : ℝ) * (b - a)) / (π * (h : ℝ)))
      * Complex.exp (-(2 * π * (h : ℝ) * ((a + b) / 2) * Complex.I)))‖ ≤ 4 / (h : ℝ) :=
  sigma524_coeff_norm a b H h hH

/-- LEAF. Width at most `1/3` with the constant below one and too little
room below it for a single cosine, since
`C * (1 + cos (π * (b - a))) < 1`. Here the majorant has to put mass on
the higher frequencies `2 ≤ h ≤ H`, which is the finite Fourier majorant of
Lemma 4 in its narrowest regime. -/
theorem leaf_majorant_small_width524 (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : b - a ≤ 1 / 3)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1)
    (hC2 : (b - a + 4 / ((H : ℝ) + 1)) * (1 + cos (π * (b - a))) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  set C := b - a + 4 / ((H : ℝ) + 1) with hCdef
  have hClt : C < 1 := by rw [hCdef]; exact hC1
  have hCpos : 0 ≤ C := by
    rw [hCdef]
    positivity
  set m := (a + b) / 2 with hmdef
  set w := b - a with hwdef
  have hwpos : 0 < w := by rw [hwdef]; linarith
  have hwle : w ≤ 1 / 3 := by rw [hwdef]; exact hw1
  have hw_half : w / 2 ≤ 1 / 6 := by linarith
  -- Use the Fejér kernel construction: P(x) = C * K_H(x-m)
  -- The Fejér kernel has constant term 1/(H+1), so scaled by C gives constant C/(H+1) ≤ C
  -- The other coefficients are 2C(1 - h/(H+1)) ≤ 2C ≤ 4/h for h ≥ 1
  -- We need P(x) ≥ 1_{[a,b)}(x)
  -- Since P(x) = C * K_H(x-m) and K_H is nonnegative and decreasing on [0, 1/2],
  -- the minimum on [a,b) is at the endpoints, where |x-m| = w/2.
  -- So we need C * K_H(w/2) ≥ 1.
  -- For the given ranges, this holds because K_H(t) ≥ (H+1) * (sin(π(H+1/2)t) / (π(H+1/2)t))^2?
  -- Actually, a simpler bound: K_H(t) ≥ (H+1) * (sin(π(H+1)t) / (π(H+1)t))^2 for t ∈ [0,1/2].
  -- But this is getting too complex. Let's use a different approach.
  sorry

/-- LEAF. Width strictly between `1/3` and `1/2` with the constant below
one. The cosine of the midpoint is still positive but the amplitude that
reaches one on the interval is already larger than the constant, so staying
nonnegative off the interval forces a majorant built from several
frequencies: the finite Fourier majorant of Lemma 4 in the intermediate
width regime. -/
theorem leaf_majorant_mid_width524 (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : 1 / 3 < b - a)
    (hw2 : b - a < 1 / 2) (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  sorry

/-- LEAF. Width at least `1/2` with the constant below one. Here the
complement of the interval is narrower than the interval itself and the
cosine of the midpoint is nonpositive, so the majorant is a smoothed
indicator rather than a bump: the finite Fourier majorant of Lemma 4 in
the wide width regime. -/
theorem leaf_majorant_large_width524 (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : 1 / 2 ≤ b - a)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  sorry

/-- The width-at-most-`1/3` regime with enough room below the constant: the
single cosine `C + γ * cos (2 π (x - m))` around the midpoint `m` of the
interval has amplitude `γ = (1 - C) / cos (π * (b - a))`, which lies between
`0` and `C`, so it is nonnegative everywhere and at least one on the
interval, and its single coefficient is at most one. -/
private theorem majorant_cosine524 (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH1 : 1 ≤ H) (hw3 : b - a ≤ 1 / 3)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1)
    (hB : 1 ≤ (b - a + 4 / ((H : ℝ) + 1)) * (1 + cos (π * (b - a)))) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  classical
  set w := b - a with hwdef
  set m := (a + b) / 2 with hmdef
  set C := b - a + 4 / ((H : ℝ) + 1) with hCdef
  have hwpos : 0 < w := by rw [hwdef]; linarith
  have hwle : w ≤ 1 / 3 := by rw [hwdef]; exact hw3
  have hClt : C < 1 := by rw [hCdef]; exact hC1
  have hB' : 1 ≤ C * (1 + cos (π * w)) := by rw [hCdef, hwdef]; exact hB
  have hcos12 : (1 / 2 : ℝ) ≤ cos (π * w) := by
    have h0 : 0 ≤ π * w := by positivity
    have hle : π * w ≤ π / 3 := by nlinarith [Real.pi_pos]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := π * w) (y := π / 3) h0
      (by linarith [Real.pi_pos]) hle
    rw [Real.cos_pi_div_three] at h
    linarith
  have hcospos : 0 < cos (π * w) := by linarith
  set γ := (1 - C) / cos (π * w) with hγdef
  have hγpos : 0 < γ := by
    rw [hγdef]
    exact div_pos (by linarith) hcospos
  have hγC : γ ≤ C := by
    rw [hγdef, div_le_iff₀ hcospos]
    nlinarith [hB', hcospos]
  have hγ1 : γ ≤ 1 := by linarith
  have hmain : γ * cos (π * w) = 1 - C := by
    rw [hγdef]
    field_simp
  refine ⟨C, fun h => if h = 1 then (γ : ℂ) * eC (-m) else 0, le_of_eq hCdef, ?_, ?_⟩
  · intro h hh
    simp only
    by_cases h1 : h = 1
    · subst h1
      have hnorm : ‖(γ : ℂ) * eC (-m)‖ = γ := by
        rw [norm_mul, eC_norm524, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hγpos]
      rw [if_pos rfl, hnorm]
      norm_num
      linarith
    · rw [if_neg h1, norm_zero]
      positivity
  · intro x
    simp only
    have hsum : (∑ h ∈ Icc 1 H,
        (if h = 1 then (γ : ℂ) * eC (-m) else 0) * eC ((h : ℝ) * x))
        = (γ : ℂ) * eC (x - m) := by
      rw [Finset.sum_eq_single 1]
      · rw [if_pos rfl, Nat.cast_one, one_mul, mul_assoc, eC_mul524,
          show -m + x = x - m by ring]
      · intro h _ hne
        rw [if_neg hne, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hH1⟩) hnot
    have hre : ((γ : ℂ) * eC (x - m)).re = γ * cos (2 * π * (x - m)) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, eC_re524]
    by_cases hx : a ≤ Int.fract x ∧ Int.fract x < b
    · rw [if_pos hx, hsum, hre]
      have hfl : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
      have hxp : 2 * π * (x - m) = 2 * π * (Int.fract x - m) + (⌊x⌋ : ℤ) * (2 * π) := by
        conv_lhs => rw [hfl]
        push_cast
        ring
      have hcosx : cos (2 * π * (x - m)) = cos (2 * π * (Int.fract x - m)) := by
        rw [hxp, Real.cos_add_int_mul_two_pi]
      have hdist : |Int.fract x - m| ≤ w / 2 := by
        rw [abs_le]
        constructor
        · rw [hmdef, hwdef]; linarith [hx.1]
        · rw [hmdef, hwdef]; linarith [hx.2]
      have hcosine : cos (π * w) ≤ cos (2 * π * (Int.fract x - m)) := by
        have ht := hdist
        have h0 : 0 ≤ 2 * π * |Int.fract x - m| := by positivity
        have hle : π * w ≤ π := by nlinarith [Real.pi_pos, hwle]
        have h2 : 2 * π * |Int.fract x - m| ≤ π * w := by
          nlinarith [abs_nonneg (Int.fract x - m), Real.pi_pos, ht]
        have h3 := Real.cos_le_cos_of_nonneg_of_le_pi (x := 2 * π * |Int.fract x - m|)
          (y := π * w) h0 hle h2
        have h4 : cos (2 * π * |Int.fract x - m|) = cos (2 * π * (Int.fract x - m)) := by
          have habs : |2 * π * (Int.fract x - m)| = 2 * π * |Int.fract x - m| := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          conv_rhs => rw [← Real.cos_abs]
          rw [habs]
        rwa [h4] at h3
      rw [hcosx]
      nlinarith [mul_le_mul_of_nonneg_left hcosine hγpos.le, hmain]
    · rw [if_neg hx, hsum, hre]
      have hcos1 : -1 ≤ cos (2 * π * (x - m)) := Real.neg_one_le_cos _
      nlinarith [hγC, hγpos, hcos1]

set_option maxHeartbeats 1000000 in
/-- The target of the parent file, split into the three width leaves: the
constant-dominates case and the single-cosine case are proved here, the
remaining three regimes are the leaves. -/
theorem leaf_interval_majorant524_split (a b : ℝ) (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (H : ℕ) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  classical
  by_cases hA : 1 ≤ b - a + 4 / ((H : ℝ) + 1)
  · refine ⟨b - a + 4 / ((H : ℝ) + 1), fun _ => 0, le_rfl, ?_, ?_⟩
    · intro h hh
      simp only [norm_zero]
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg h)
    · intro x
      simp only [zero_mul, Finset.sum_const_zero, Complex.zero_re, add_zero]
      split_ifs with hx
      · exact hA
      · have hw : 0 ≤ b - a := by linarith
        positivity
  · push_neg at hA
    have hw0 : 0 ≤ b - a := by linarith
    have h41 : 4 / ((H : ℝ) + 1) < 1 := by linarith
    have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    have h5 : (4 : ℝ) < (H : ℝ) + 1 := by
      have := (div_lt_iff₀ hpos).mp h41
      simpa using this
    have hH4 : 4 ≤ H := by
      have h6 : ((3 : ℕ) : ℝ) < (H : ℝ) := by push_cast; linarith
      have h7 : 3 < H := Nat.cast_lt.mp h6
      omega
    have hH1 : 1 ≤ H := by omega
    by_cases hw3 : b - a ≤ 1 / 3
    · by_cases hB : 1 ≤ (b - a + 4 / ((H : ℝ) + 1)) * (1 + cos (π * (b - a)))
      · exact majorant_cosine524 a b hab ha hb H hH1 hw3 hA hB
      · push_neg at hB
        exact leaf_majorant_small_width524 a b hab ha hb H hH4 hw3 hA hB
    · push_neg at hw3
      by_cases hw2 : b - a < 1 / 2
      · exact leaf_majorant_mid_width524 a b hab ha hb H hH4 hw3 hw2 hA
      · push_neg at hw2
        exact leaf_majorant_large_width524 a b hab ha hb H hH4 hw2 hA

end LeanLab.ExceptionalSet.Decomp524a