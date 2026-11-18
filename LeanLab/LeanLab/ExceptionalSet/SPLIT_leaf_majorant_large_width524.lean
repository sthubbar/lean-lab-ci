import LeanLab.ExceptionalSet.SPLIT_leaf_interval_majorant524

/-!
Split of `LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_large_width524`.

The target covers the regime where the interval `[a, b)` has width at least
one half while the constant `C = b - a + 4 / (H + 1)` is still below one. The
majorant found in the target file there can no longer be a single cosine
centred at the midpoint, since `cos (π * (b - a)) ≤ 0` forces the amplitude of
that cosine to be negative.

This file cuts the target into a normalisation step and the existence input
that remains. The interval is moved to start at the origin, where the
indicator is `fract x < b - a`: the coefficients are rotated by the phase
`eC (-(h * a))`, which leaves every coefficient norm unchanged and turns the
shift of the argument into a shift of the window. The existence of a majorant
for the window put at the origin is the single remaining leaf; the two
further regimes are the structure of that majorant, which has to put mass on
the higher frequencies to stay nonnegative where the indicator drops to zero.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- `eC` turns sums of arguments into products. -/
private theorem eC_add524 (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `eC` has modulus one. -/
private theorem eC_norm524 (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- The fractional part drops the shift `a` as soon as `a` does not exceed it. -/
private theorem fract_sub_shift524 (x a : ℝ) (h0 : 0 ≤ Int.fract x - a)
    (h1 : Int.fract x - a < 1) : Int.fract (x - a) = Int.fract x - a := by
  rw [Int.fract_eq_iff]
  refine ⟨h0, h1, ⌊x⌋, ?_⟩
  linarith [Int.fract_add_floor x]

/-- LEAF. The indicator of the window `[a, a + w)` agrees, at the level of
fractional parts, with the normalised indicator `fract (x - a) < w` of the
window `[0, w)` placed at the origin. Both directions are step identities:
one shift of the argument against one shift of the window. -/
theorem leaf_large_width_fract_shift524 (x a w : ℝ) (ha : 0 ≤ a) (hw : a + w ≤ 1) :
    (a ≤ Int.fract x ∧ Int.fract x < a + w) ↔ Int.fract (x - a) < w := by
  have hlt1 : Int.fract x < 1 := Int.fract_lt_one x
  have hnn : 0 ≤ Int.fract x := Int.fract_nonneg x
  constructor
  · rintro ⟨h1, h2⟩
    rw [fract_sub_shift524 x a (by linarith) (by linarith)]
    linarith
  · intro h
    by_cases hge : a ≤ Int.fract x
    · rw [fract_sub_shift524 x a (by linarith) (by linarith)] at h
      exact ⟨hge, by linarith⟩
    · push_neg at hge
      have hwpos : 0 < w := lt_of_le_of_lt (Int.fract_nonneg (x - a)) h
      have ha1 : a < 1 := by linarith
      exfalso
      have hkey : Int.fract (x - a) = Int.fract x - a + 1 := by
        have hper : Int.fract (x - a) = Int.fract (Int.fract x - a) := by
          rw [Int.fract_eq_fract]
          exact ⟨⌊x⌋, by push_cast; linarith [Int.fract_add_floor x]⟩
        rw [hper, Int.fract_eq_iff]
        exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
      rw [hkey] at h
      linarith

/-- Rotation of the phase of one coefficient by `a` shifts the argument of
the exponential by `a`. -/
private theorem shift_term524 (c : ℕ → ℂ) (a x : ℝ) (h : ℕ) :
    c h * eC (-((h : ℝ) * a)) * eC ((h : ℝ) * x) = c h * eC ((h : ℝ) * (x - a)) := by
  rw [mul_assoc, ← eC_add524]
  congr 1
  ring

/-- LEAF. Transport of a majorant from the window at the origin to the window
`[a, b)`: rotating every coefficient by `eC (-(h * a))` keeps all coefficient
norms, keeps the constant, and shifts the argument of the exponential sum by
`a`, so domination of the normalised indicator becomes domination of the
indicator of `[a, b)`. -/
theorem leaf_large_width_shift524 (a b : ℝ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (H : ℕ)
    (hcore : ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if Int.fract x < b - a then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  obtain ⟨c₀, c, hc₀, hc, hdom⟩ := hcore
  have hc' : ∀ h ∈ Icc 1 H, ‖(fun h => c h * eC (-((h : ℝ) * a))) h‖ ≤ 4 / (h : ℝ) := by
    intro h hh
    rw [norm_mul, eC_norm524, mul_one]
    exact hc h hh
  have hdom' : ∀ x : ℝ,
      (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H,
          (fun h => c h * eC (-((h : ℝ) * a))) h * eC ((h : ℝ) * x)).re := by
    intro x
    have hiff : (a ≤ Int.fract x ∧ Int.fract x < b) ↔ Int.fract (x - a) < b - a := by
      have h' := leaf_large_width_fract_shift524 x a (b - a) ha (by linarith)
      rwa [show a + (b - a) = b by ring] at h'
    have hd := hdom (x - a)
    simp only [shift_term524] at hd ⊢
    split_ifs with hx
    · have hx' : Int.fract (x - a) < b - a := hiff.mp hx
      simp only [if_pos hx'] at hd
      exact hd
    · have hx' : ¬ (Int.fract (x - a) < b - a) := fun hc' => hx (hiff.mpr hc')
      simp only [if_neg hx'] at hd
      exact hd
  exact ⟨c₀, fun h => c h * eC (-((h : ℝ) * a)), hc₀, hc', hdom'⟩

/-! ### The Selberg type majorant on the grid `j / (H + 1)`

The exponential lemmas below were moved up, unchanged, from the critical-grid section so
that the construction can use them. The majorant is the sum of the Fejér kernels at the grid
nodes `0, …, m` with `m = ⌈w (H + 1)⌉`, plus the conjugate sine correction
`(π (H + 1))⁻¹ ∑ (sin (2 π h x) - sin (2 π h (x - m / (H + 1))))`; this is Selberg's majorant
of the indicator of `[0, m / (H + 1)]`, see Montgomery, Ten Lectures, Chapter 1, and Vaaler,
Bull. AMS 12 (1985). Its mean is `(m + 1) / (H + 1) < w + 2 / (H + 1)`. -/

/-- `eC` written as an exponential. -/
private theorem eC_eq524c (t : ℝ) :
    eC t = Complex.exp ((2 * π * t : ℝ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

/-- The real part of `eC` is a cosine. -/
private theorem eC_re524c (t : ℝ) : (eC t).re = cos (2 * π * t) := by
  rw [eC_eq524c, Complex.exp_ofReal_mul_I_re]

/-- `eC` turns sums into products. -/
private theorem eC_mul524c (s t : ℝ) : eC s * eC t = eC (s + t) := by
  simp only [eC_eq524c, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Powers of `eC` add the arguments. -/
private theorem eC_pow524c (t : ℝ) (n : ℕ) : (eC t) ^ n = eC (n * t) := by
  induction n with
  | zero => simp [eC_eq524c]
  | succ k ih =>
      rw [pow_succ, ih, eC_mul524c]
      congr 1
      push_cast
      ring

/-- `eC` of a natural number is one. -/
private theorem eC_nat524c (n : ℕ) : eC (n : ℝ) = 1 := by
  rw [eC_eq524c]
  have hEq : ((2 * π * (n : ℝ) : ℝ) * Complex.I) = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hEq, Complex.exp_nat_mul_two_pi_mul_I]

/-- `eC` takes the value one only at integers, so not on the open unit interval. -/
private theorem eC_ne_one524c (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : eC t ≠ 1 := by
  intro h
  have h1' : Complex.exp ((2 * π * t : ℝ) * Complex.I) = 1 := by
    rw [← eC_eq524c]
    exact h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1'
  have hR : ((2 * π * t : ℝ) : ℂ) * Complex.I = (((n : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I := by
    rw [hn]
    push_cast
    ring
  have hreal : (2 * π * t : ℝ) = (n : ℝ) * (2 * π) := by
    have hc := mul_right_cancel₀ Complex.I_ne_zero hR
    exact Complex.ofReal_injective hc
  have ht : t = (n : ℝ) := by nlinarith [Real.pi_pos]
  have hpos : (0 : ℤ) < n := by
    have : (0 : ℝ) < (n : ℝ) := by rw [← ht]; exact h0
    exact_mod_cast this
  have hone : (1 : ℤ) ≤ n := Int.lt_iff_add_one_le.mp hpos
  have hge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hone
  linarith

/-- The root-of-unity sum in complex form: for `1 ≤ h ≤ N - 1` the `N`-th roots of
unity cancel, so the exponential sum over the critical grid vanishes. -/
private theorem eC_grid_sum524c (h N : ℕ) (hh1 : 1 ≤ h) (hhN : h ≤ N - 1) :
    (∑ j ∈ Finset.range N, eC ((h : ℝ) * ((j : ℝ) / N))) = 0 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  set ζ : ℂ := eC ((h : ℝ) / N) with hζ
  have hζne : ζ ≠ 1 := by
    rw [hζ]
    refine eC_ne_one524c _ (by positivity) ?_
    rw [div_lt_one hNpos]
    exact_mod_cast (by omega : h < N)
  have hζN : ζ ^ N = 1 := by
    rw [hζ, eC_pow524c]
    have hcast : (N : ℝ) * ((h : ℝ) / N) = (h : ℝ) := by field_simp
    rw [hcast, eC_nat524c]
  have hsum : (∑ j ∈ Finset.range N, ζ ^ j) = 0 := by
    have hg := geom_sum_eq hζne N
    rw [hζN, sub_self, zero_div] at hg
    exact hg
  have hterm : ∀ j : ℕ, eC ((h : ℝ) * ((j : ℝ) / N)) = ζ ^ j := by
    intro j
    rw [hζ, eC_pow524c]
    congr 1
    have : (h : ℝ) * ((j : ℝ) / N) = (j : ℝ) * ((h : ℝ) / N) := by field_simp
    rw [this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), hsum]

/-- A1a. Dirichlet kernel in closed form. -/
private theorem dirichlet524s (n : ℕ) (y : ℝ) :
    sin (π * y) * (1 + 2 * ∑ h ∈ Icc 1 n, cos (2 * π * (h : ℝ) * y))
      = sin ((2 * (n : ℝ) + 1) * (π * y)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, mul_add] at *
    push_cast
    have e1 : 2 * π * ((n : ℝ) + 1) * y = (2 * (n : ℝ) + 2) * (π * y) := by ring
    have e2 : (2 * ((n : ℝ) + 1) + 1) * (π * y)
        = (2 * (n : ℝ) + 2) * (π * y) + π * y := by ring
    have e3 : (2 * (n : ℝ) + 1) * (π * y) = (2 * (n : ℝ) + 2) * (π * y) - π * y := by ring
    rw [e3] at ih
    rw [e1, e2, sin_add]
    rw [sin_sub] at ih
    linear_combination ih

/-- A1b. Fejér kernel in closed form, cleared of denominators. -/
private theorem fejer524s (H : ℕ) (y : ℝ) :
    sin (π * y) ^ 2 * (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H,
        (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * y))
      = sin (((H : ℝ) + 1) * (π * y)) ^ 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hd := dirichlet524s (H + 1) y
    have hsplit : ∑ h ∈ Icc 1 (H + 1), ((((H + 1 : ℕ) : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * y)
        = ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * y)
          + ∑ h ∈ Icc 1 (H + 1), cos (2 * π * (h : ℝ) * y) := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        ← add_assoc, ← Finset.sum_add_distrib]
      push_cast
      congr 1
      · apply Finset.sum_congr rfl
        intro h _
        ring
      · ring
    rw [hsplit]
    push_cast at hd ⊢
    have e2 : (2 * ((H : ℝ) + 1) + 1) * (π * y)
        = ((H : ℝ) + 1) * (π * y) + (((H : ℝ) + 1) * (π * y) + π * y) := by ring
    have e3 : ((H : ℝ) + 1 + 1) * (π * y) = ((H : ℝ) + 1) * (π * y) + π * y := by ring
    rw [e2] at hd
    rw [e3]
    rw [sin_add, sin_add, cos_add] at hd
    rw [sin_add]
    have h1 := sin_sq_add_cos_sq (π * y)
    linear_combination ih + sin (π * y) * hd
      - (sin (((H : ℝ) + 1) * (π * y)) ^ 2) * h1

/-- A1c. Conjugate sine sum in closed form, cleared of denominators. -/
private theorem conj524s (H : ℕ) (y : ℝ) :
    sin (π * y) * ∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * y)
      = sin (((H : ℝ) + 1) * (π * y)) ^ 2 * cos (π * y)
        - sin (((H : ℝ) + 1) * (π * y)) * cos (((H : ℝ) + 1) * (π * y)) * sin (π * y) := by
  induction H with
  | zero => simp; ring
  | succ H ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast
    have e1 : 2 * π * ((H : ℝ) + 1) * y = 2 * (((H : ℝ) + 1) * (π * y)) := by ring
    have e3 : ((H : ℝ) + 1 + 1) * (π * y) = ((H : ℝ) + 1) * (π * y) + π * y := by ring
    rw [e1, e3, sin_two_mul, sin_add, cos_add]
    have h1 := sin_sq_add_cos_sq (π * y)
    linear_combination (-(sin (((H : ℝ) + 1) * (π * y)) * cos (π * y)
      + cos (((H : ℝ) + 1) * (π * y)) * sin (π * y)) * sin (((H : ℝ) + 1) * (π * y))) * h1

private theorem trapStep524s (N : ℝ) (hN : 1 ≤ N) (u : ℝ) (hb : 0 < sin (π * u))
    (ha : 0 < sin (π * (u - 1 / N))) :
    N / π * (cos (π * (u - 1 / N)) / sin (π * (u - 1 / N)) - cos (π * u) / sin (π * u))
      ≤ 1 / 2 * (1 / sin (π * u) ^ 2 + 1 / sin (π * (u - 1 / N)) ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hpi : 0 < π := Real.pi_pos
  have hs : sin (π / N) = sin (π * u) * cos (π * (u - 1 / N))
      - cos (π * u) * sin (π * (u - 1 / N)) := by
    rw [← Real.sin_sub]; congr 1; field_simp; ring
  have hle : sin (π / N) ≤ π / N := Real.sin_le (by positivity)
  have h2 : N / π * sin (π / N) ≤ 1 := by
    have h : N / π * sin (π / N) ≤ N / π * (π / N) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h' : N / π * (π / N) = 1 := by field_simp
    linarith
  generalize sin (π * (u - 1 / N)) = a at *
  generalize sin (π * u) = b at *
  generalize cos (π * (u - 1 / N)) = c at *
  generalize cos (π * u) = d at *
  have hab : 0 < a * b := mul_pos ha hb
  have h1 : N / π * (c / a - d / b) = (N / π * sin (π / N)) / (a * b) := by
    rw [hs]; field_simp
  rw [h1]
  have h3 : (N / π * sin (π / N)) / (a * b) ≤ 1 / (a * b) :=
    div_le_div_of_nonneg_right h2 hab.le
  have h4 : 1 / (a * b) ≤ 1 / 2 * (1 / b ^ 2 + 1 / a ^ 2) := by
    have e : 1 / 2 * (1 / b ^ 2 + 1 / a ^ 2) - 1 / (a * b) = (a - b) ^ 2 / (2 * (a * b) ^ 2) := by
      field_simp; ring
    have : 0 ≤ (a - b) ^ 2 / (2 * (a * b) ^ 2) := by positivity
    linarith
  linarith

private theorem trapStrong524s (N : ℝ) (hN : 1 ≤ N) (y : ℝ) (m : ℕ)
    (h1 : (m : ℝ) / N < y) (h2 : y < 1) :
    N / π * (cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N))
        - cos (π * y) / sin (π * y))
      + 1 / 2 * (1 / sin (π * y) ^ 2 + 1 / sin (π * (y - (m : ℝ) / N)) ^ 2)
      ≤ ∑ j ∈ range (m + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hpi : 0 < π := Real.pi_pos
  induction m with
  | zero =>
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_div, sub_zero, sub_self, mul_zero,
      zero_add]
    apply le_of_eq; ring
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ (m : ℝ) / N := by positivity
    have e : y - ((m + 1 : ℕ) : ℝ) / N = (y - (m : ℝ) / N) - 1 / N := by
      push_cast; ring
    have h1' : (m : ℝ) / N < y := by
      have : (0 : ℝ) < 1 / N := by positivity
      linarith [e]
    have ih' := ih h1'
    rw [Finset.sum_range_succ, e]
    have hu0 : 0 < y - (m : ℝ) / N - 1 / N := by linarith [e]
    have hb : 0 < sin (π * (y - (m : ℝ) / N)) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi (by linarith)) (by nlinarith)
    have ha : 0 < sin (π * (y - (m : ℝ) / N - 1 / N)) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hu0) (by
        have : (0 : ℝ) < 1 / N := by positivity
        nlinarith)
    have hst := trapStep524s N hN (y - (m : ℝ) / N) hb ha
    linarith

/-- A2. Trapezoid comparison: the cotangent difference over `m` steps of length `1 / N`
is at most the sum of `1 / sin ^ 2` over the `m + 1` nodes. -/
private theorem trapezoid524s (N : ℝ) (hN : 1 ≤ N) (y : ℝ) (m : ℕ)
    (h1 : (m : ℝ) / N < y) (h2 : y < 1) :
    N / π * (cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N))
        - cos (π * y) / sin (π * y))
      ≤ ∑ j ∈ range (m + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2 := by
  have h := trapStrong524s N hN y m h1 h2
  have : 0 ≤ 1 / 2 * (1 / sin (π * y) ^ 2 + 1 / sin (π * (y - (m : ℝ) / N)) ^ 2) := by
    positivity
  linarith

private theorem step524s (N : ℝ) (hN : 2 ≤ N) (u : ℝ)
    (h1 : -1 < u - 1 / (2 * N)) (h2 : u + 1 / (2 * N) < 0) :
    1 / sin (π * u) ^ 2
      ≤ N / π * (cos (π * (u - 1 / (2 * N))) / sin (π * (u - 1 / (2 * N)))
          - cos (π * (u + 1 / (2 * N))) / sin (π * (u + 1 / (2 * N)))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hpi := Real.pi_pos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = π / (2 * N) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht4 : t ≤ π / 4 := by
    rw [ht, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have ea : π * (u - 1 / (2 * N)) = π * u - t := by rw [ht]; ring
  have eb : π * (u + 1 / (2 * N)) = π * u + t := by rw [ht]; ring
  have eN : N / π = 1 / (2 * t) := by rw [ht]; field_simp
  have hs1 : sin (π * u - t) < 0 := by
    rw [← ea]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · have : u - 1 / (2 * N) < 0 := by
        have : (0 : ℝ) < 1 / (2 * N) := by positivity
        linarith
      nlinarith
    · nlinarith
  have hs2 : sin (π * u + t) < 0 := by
    rw [← eb]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith
    · have : -1 < u + 1 / (2 * N) := by
        have : (0 : ℝ) < 1 / (2 * N) := by positivity
        linarith
      nlinarith
  rw [ea, eb, eN]
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = sin (π * u) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = cos (π * u) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = sin t := ⟨_, rfl⟩
  obtain ⟨c, hcc⟩ : ∃ c : ℝ, c = cos t := ⟨_, rfl⟩
  have hSC : S ^ 2 + C ^ 2 = 1 := by rw [hS, hC]; exact Real.sin_sq_add_cos_sq _
  have hsc : s ^ 2 + c ^ 2 = 1 := by rw [hs, hcc]; exact Real.sin_sq_add_cos_sq _
  have hs0 : 0 ≤ s := by
    rw [hs]; exact Real.sin_nonneg_of_nonneg_of_le_pi ht0.le (by linarith)
  have hc0 : 0 < c := by
    rw [hcc]; exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc1 : c ≤ 1 := by rw [hcc]; exact Real.cos_le_one _
  have hst : s ≤ t := by rw [hs]; exact Real.sin_le ht0.le
  have htc : t * c ≤ s := by
    have h := Real.lt_tan ht0 (by linarith)
    rw [Real.tan_eq_sin_div_cos, ← hs, ← hcc, lt_div_iff₀ hc0] at h
    exact h.le
  rw [Real.sin_sub, ← hS, ← hC, ← hs, ← hcc] at hs1
  rw [Real.sin_add, ← hS, ← hC, ← hs, ← hcc] at hs2
  rw [Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add, ← hS, ← hC, ← hs, ← hcc]
  have hD : (S * c - C * s) * (S * c + C * s) = S ^ 2 - s ^ 2 := by
    have : C ^ 2 = 1 - S ^ 2 := by linarith
    have : c ^ 2 = 1 - s ^ 2 := by linarith
    nlinarith
  have hDpos : 0 < S ^ 2 - s ^ 2 := by rw [← hD]; exact mul_pos_of_neg_of_neg hs1 hs2
  have hSpos : 0 < S ^ 2 := by nlinarith [sq_nonneg s]
  have hS1 : S ^ 2 ≤ 1 := by nlinarith [sq_nonneg C]
  have hdiff : (C * c + S * s) / (S * c - C * s) - (C * c - S * s) / (S * c + C * s)
      = 2 * s * c / (S ^ 2 - s ^ 2) := by
    rw [div_sub_div _ _ hs1.ne hs2.ne, hD]
    congr 1
    linear_combination (2 * s * c) * hSC
  rw [hdiff, div_mul_div_comm, div_le_div_iff₀ hSpos (mul_pos (by linarith) hDpos : 0 < 2 * t * (S ^ 2 - s ^ 2))]
  have h1' : 0 ≤ t - s * c := by nlinarith
  have h2' : t * c ^ 2 ≤ s * c := by nlinarith
  have h3' : S ^ 2 * (t - s * c) ≤ t - s * c := by nlinarith
  have h4' : t * c ^ 2 = t - t * s ^ 2 := by
    have : c ^ 2 = 1 - s ^ 2 := by linarith
    rw [this]; ring
  have h5' : S ^ 2 * (t - s * c) ≤ t * s ^ 2 := by linarith
  linarith [h5']

/-- A3. Midpoint comparison: the sum of `1 / sin ^ 2` over nodes `a, …, a + n - 1` is at
most the cotangent difference over the cells centred at those nodes. -/
private theorem midpoint524s (N : ℝ) (hN : 2 ≤ N) (y : ℝ) (a n : ℕ)
    (h1 : y - (a : ℝ) / N + 1 / (2 * N) < 0)
    (h2 : -1 < y - ((a : ℝ) + n) / N + 1 / (2 * N)) :
    ∑ j ∈ Ico a (a + n), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2
      ≤ N / π * (cos (π * (y - ((a : ℝ) + n) / N + 1 / (2 * N)))
            / sin (π * (y - ((a : ℝ) + n) / N + 1 / (2 * N)))
          - cos (π * (y - (a : ℝ) / N + 1 / (2 * N)))
            / sin (π * (y - (a : ℝ) / N + 1 / (2 * N)))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc] at h2 ⊢
    have hinv : (0 : ℝ) < 1 / N := by positivity
    have hnN : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    have e1 : ((a : ℝ) + ((n : ℝ) + 1)) / N = ((a : ℝ) + n) / N + 1 / N := by ring
    have e2 : ((a : ℝ) + n) / N = (a : ℝ) / N + (n : ℝ) / N := by ring
    have e3 : 1 / (2 * N) = (1 / N) / 2 := by field_simp
    have ih' := ih (by rw [e1] at h2; linarith)
    have hst := step524s N hN (y - ((a : ℝ) + n) / N)
      (by rw [e1] at h2; rw [e3] at h2 ⊢; linarith)
      (by rw [e2]; linarith)
    have e4 : y - ((a : ℝ) + n) / N - 1 / (2 * N)
        = y - ((a : ℝ) + ((n : ℝ) + 1)) / N + 1 / (2 * N) := by
      rw [e1, e3]; ring
    rw [e4] at hst
    rw [show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    have hcast : (((a + n : ℕ)) : ℝ) = (a : ℝ) + n := by push_cast; ring
    rw [hcast]
    have hpos : 0 < N / π := div_pos hN0 Real.pi_pos
    nlinarith [ih', hst]

private theorem jordan524s (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * t * (1 - t) ≤ sin (π * t) := by
  have hpi := Real.pi_pos
  rcases le_total t (1/2) with ht | ht
  · have := Real.mul_le_sin (x := π*t) (by positivity) (by nlinarith)
    have e : 2/π*(π*t) = 2*t := by field_simp
    rw [e] at this; nlinarith
  · have := Real.mul_le_sin (x := π*(1-t)) (mul_nonneg hpi.le (by linarith)) (by nlinarith)
    have e : 2/π*(π*(1-t)) = 2*(1-t) := by field_simp
    have e2 : sin (π*(1-t)) = sin (π*t) := by
      rw [show π*(1-t) = π - π*t by ring, Real.sin_pi_sub]
    rw [e, e2] at this; nlinarith

private theorem eC_sub_one_norm524s (t : ℝ) : 2 * sin (π*t) ≤ ‖eC (-t) - 1‖ := by
  have hre : (eC (-t) - 1).re = cos (2*(π*t)) - 1 := by
    rw [Complex.sub_re, eC_re524c, Complex.one_re]
    have : 2*π*(-t) = -(2*(π*t)) := by ring
    rw [this, Real.cos_neg]
  have him : (eC (-t) - 1).im = -sin (2*(π*t)) := by
    rw [Complex.sub_im, eC_eq524c, Complex.exp_ofReal_mul_I_im, Complex.one_im]
    have : 2*π*(-t) = -(2*(π*t)) := by ring
    rw [this, Real.sin_neg, sub_zero]
  have hsq : ‖eC (-t) - 1‖^2 = 4 * sin (π*t)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (4*cos (π*t)^2 - 4) * Real.sin_sq_add_cos_sq (π*t)
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg (eC (-t) - 1)]

/-- A4. Coefficient bound. -/
private theorem coeff_bound524s (H m h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ H) :
    ‖(((2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ)) : ℝ)) : ℂ)
          * ∑ j ∈ range (m + 1), eC (-((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
          * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1)))))‖ ≤ 4 / (h : ℝ) := by
  have hN : (0:ℝ) < (H:ℝ)+1 := by positivity
  have hhN : (h:ℝ) < (H:ℝ)+1 := by
    have : (h:ℝ) ≤ H := by exact_mod_cast hhH
    linarith
  have hh0 : (0:ℝ) < h := by exact_mod_cast hh1
  generalize (H:ℝ)+1 = N at hN hhN ⊢
  have hζn : ‖eC (-((h:ℝ)/N))‖ = 1 := eC_norm524 _
  have hz := eC_sub_one_norm524s ((h:ℝ)/N)
  generalize hζ : eC (-((h:ℝ)/N)) = ζ at hζn hz
  have hterm : ∀ j:ℕ, eC (-((h:ℝ)*((j:ℝ)/N))) = ζ^j := by
    intro j
    rw [← hζ, eC_pow524c]
    congr 1
    ring
  simp only [hterm]
  have hgeo : (∑ j ∈ range (m+1), ζ^j) * (ζ - 1) = ζ^(m+1) - 1 := geom_sum_mul ζ (m+1)
  generalize (∑ j ∈ range (m+1), ζ^j) = S at hgeo ⊢
  have hSn : ‖S‖ * ‖ζ-1‖ ≤ 2 := by
    rw [← norm_mul, hgeo]
    calc ‖ζ^(m+1) - 1‖ ≤ ‖ζ^(m+1)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
  have hjor := jordan524s ((h:ℝ)/N) (by positivity) (by rw [div_le_one hN]; exact hhN.le)
  have hah : 2/N^2*(N-h) * h ≤ sin (π*((h:ℝ)/N)) := by
    have : 2/N^2*(N-h)*h = 2*((h:ℝ)/N)*(1-(h:ℝ)/N) := by field_simp
    rw [this]; exact hjor
  have ha0 : 0 ≤ 2/N^2*(N-h) := mul_nonneg (by positivity) (by linarith)
  have hSs : ‖S‖ * sin (π*((h:ℝ)/N)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hz (norm_nonneg S)
    nlinarith
  have h1 : 2/N^2*(N-h) * ‖S‖ ≤ 1/(h:ℝ) := by
    rw [le_div_iff₀ hh0]
    calc 2/N^2*(N-h) * ‖S‖ * h = (2/N^2*(N-h) * h) * ‖S‖ := by ring
      _ ≤ sin (π*((h:ℝ)/N)) * ‖S‖ := mul_le_mul_of_nonneg_right hah (norm_nonneg _)
      _ ≤ 1 := by linarith
  have h2 : 1/(π*N) * 2 ≤ 2/(h:ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hh0]
    nlinarith [mul_pos (sub_pos.2 Real.pi_gt_three) hN]
  have h3 : ‖1 - ζ^m‖ ≤ 2 := by
    calc ‖1 - ζ^m‖ ≤ ‖(1:ℂ)‖ + ‖ζ^m‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
  have hb0 : (0:ℝ) ≤ 1/(π*N) := by positivity
  calc ‖((2/N^2*(N-h) : ℝ) : ℂ)*S + ((1/(π*N):ℝ):ℂ)*(-Complex.I)*(1-ζ^m)‖
      ≤ ‖((2/N^2*(N-h) : ℝ) : ℂ)*S‖ + ‖((1/(π*N):ℝ):ℂ)*(-Complex.I)*(1-ζ^m)‖ := norm_add_le _ _
    _ = 2/N^2*(N-h)*‖S‖ + 1/(π*N) * ‖1-ζ^m‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_neg,
          Complex.norm_I, Real.norm_of_nonneg ha0, Real.norm_of_nonneg hb0, mul_one]
    _ ≤ 1/(h:ℝ) + 2/(h:ℝ) := by
        have := mul_le_mul_of_nonneg_left h3 hb0
        linarith
    _ ≤ 4/(h:ℝ) := by
        have hp : (0:ℝ) < 1/(h:ℝ) := by positivity
        have e : 4/(h:ℝ) = 4*(1/(h:ℝ)) := by ring
        have e2 : 2/(h:ℝ) = 2*(1/(h:ℝ)) := by ring
        linarith

/-- The imaginary part of `eC` is a sine. -/
private theorem eC_im524s (t : ℝ) : (eC t).im = sin (2 * π * t) := by
  rw [eC_eq524c, Complex.exp_ofReal_mul_I_im]

/-- `eC` of an integer is one. -/
private theorem eC_int524s (n : ℤ) : eC (n : ℝ) = 1 := by
  rw [eC_eq524c]
  have hEq : ((2 * π * (n : ℝ) : ℝ) * Complex.I) = (n : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hEq, Complex.exp_int_mul_two_pi_mul_I]

/-- Cosines over the grid cancel. -/
private theorem cosgrid524s (H h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ H) (y : ℝ) :
    ∑ j ∈ range (H + 1), cos (2 * π * (h : ℝ) * (y - (j : ℝ) / ((H : ℝ) + 1))) = 0 := by
  have hg := eC_grid_sum524c h (H + 1) hh1 (by omega)
  have hre : ∑ j ∈ range (H + 1), cos (2 * π * ((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1)))) = 0 := by
    have h1 := congrArg Complex.re hg
    rw [Complex.re_sum] at h1
    simp only [eC_re524c, Complex.zero_re, Nat.cast_add, Nat.cast_one] at h1
    exact h1
  have him : ∑ j ∈ range (H + 1), sin (2 * π * ((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1)))) = 0 := by
    have h1 := congrArg Complex.im hg
    rw [Complex.im_sum] at h1
    simp only [eC_im524s, Complex.zero_im, Nat.cast_add, Nat.cast_one] at h1
    exact h1
  have hterm : ∀ j : ℕ, cos (2 * π * (h : ℝ) * (y - (j : ℝ) / ((H : ℝ) + 1)))
      = cos (2 * π * (h : ℝ) * y) * cos (2 * π * ((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + sin (2 * π * (h : ℝ) * y) * sin (2 * π * ((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1)))) := by
    intro j
    rw [← Real.cos_sub]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hre, him]
  ring

/-- A5a. Real part of the complex polynomial. -/
private theorem realpart524s (H m : ℕ) (x : ℝ) :
    ((m : ℝ) + 1) / ((H : ℝ) + 1) + (∑ h ∈ Icc 1 H,
        ((((2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ)) : ℝ)) : ℂ)
          * ∑ j ∈ range (m + 1), eC (-((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
          * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1))))))
        * eC ((h : ℝ) * x)).re
      = 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1),
          (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H,
            (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1))))
        + 1 / (π * ((H : ℝ) + 1)) * (∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * x)
            - ∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * (x - (m : ℝ) / ((H : ℝ) + 1)))) := by
  have hI : ∀ z : ℂ, (-Complex.I * z).re = z.im := by
    intro z
    simp
  have hterm : ∀ h : ℕ,
      (((((2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ)) : ℝ)) : ℂ)
          * ∑ j ∈ range (m + 1), eC (-((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
          * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1))))))
        * eC ((h : ℝ) * x)).re
      = 2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ))
          * ∑ j ∈ range (m + 1), cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1)))
        + 1 / (π * ((H : ℝ) + 1)) * (sin (2 * π * (h : ℝ) * x)
            - sin (2 * π * (h : ℝ) * (x - (m : ℝ) / ((H : ℝ) + 1)))) := by
    intro h
    rw [add_mul, Complex.add_re]
    congr 1
    · rw [mul_assoc, Complex.re_ofReal_mul, Finset.sum_mul, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [eC_mul524c, eC_re524c]
      congr 1
      ring
    · have hE : (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
            * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1))))) * eC ((h : ℝ) * x)
          = (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I * (eC ((h : ℝ) * x)
              - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1))) + (h : ℝ) * x))) := by
        rw [← eC_mul524c]
        ring
      rw [hE, Complex.re_ofReal_mul, hI, Complex.sub_im, eC_im524s, eC_im524s]
      congr 3
      · ring
      · ring
  have hN : ((H : ℝ) + 1) ≠ 0 := by positivity
  have hR : ∑ j ∈ range (m + 1), (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H,
        (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1))))
      = ((m : ℝ) + 1) * ((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ))
          * ∑ j ∈ range (m + 1), cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1))) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_comm, nsmul_eq_mul]
    congr 1
    · push_cast
      ring
    · congr 1
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [Finset.mul_sum]
  have hL : ∑ h ∈ Icc 1 H, 2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ))
          * ∑ j ∈ range (m + 1), cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1)))
      = 2 / ((H : ℝ) + 1) ^ 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ))
          * ∑ j ∈ range (m + 1), cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    ring
  rw [Complex.re_sum, Finset.sum_congr rfl (fun h _ => hterm h), Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hL, hR]
  generalize (∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ))
          * ∑ j ∈ range (m + 1), cos (2 * π * (h : ℝ) * (x - (j : ℝ) / ((H : ℝ) + 1)))) = T
  generalize (∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * x)) = S1
  generalize (∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * (x - (m : ℝ) / ((H : ℝ) + 1)))) = S2
  field_simp
  ring

/-- A5b. Periodicity of an exponential polynomial. -/
private theorem periodic524s (H : ℕ) (c : ℕ → ℂ) (x : ℝ) :
    ∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)
      = ∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * Int.fract x) := by
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have hx : (h : ℝ) * x = (h : ℝ) * Int.fract x + (((h : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast
    rw [← mul_add, Int.fract_add_floor]
  rw [hx, eC_add524, eC_int524s, mul_one]

/-- A5c. Partition of unity: the Fejér kernels at the `H + 1` grid nodes sum to a constant. -/
private theorem partition524s (H : ℕ) (y : ℝ) :
    ∑ j ∈ range (H + 1), (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H,
        (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * (y - (j : ℝ) / ((H : ℝ) + 1))))
      = ((H : ℝ) + 1) ^ 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    Finset.sum_comm]
  have hz : ∀ h ∈ Icc 1 H, ∑ j ∈ range (H + 1),
      (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * (y - (j : ℝ) / ((H : ℝ) + 1))) = 0 := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    rw [← Finset.mul_sum, cosgrid524s H h hh.1 hh.2, mul_zero]
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, nsmul_eq_mul]
  push_cast
  ring

private theorem shift524s (N y : ℝ) (hN : N ≠ 0) (j : ℕ) :
    sin (N * (π * (y - (j : ℝ) / N))) ^ 2 = sin (N * (π * y)) ^ 2 ∧
    sin (N * (π * (y - (j : ℝ) / N))) * cos (N * (π * (y - (j : ℝ) / N)))
      = sin (N * (π * y)) * cos (N * (π * y)) := by
  have e0 : N * (π * ((j : ℝ) / N)) = (j : ℝ) * π := by
    field_simp
  have e : N * (π * (y - (j : ℝ) / N)) = N * (π * y) - (j : ℝ) * π := by
    rw [mul_sub, mul_sub, e0]
  rw [e, Real.sin_sub_nat_mul_pi, Real.cos_sub_nat_mul_pi]
  have hpm : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  constructor
  · linear_combination (sin (N * (π * y))) ^ 2 * hpm
  · linear_combination sin (N * (π * y)) * cos (N * (π * y)) * hpm

private theorem phival524s (N z : ℝ) (Φ : ℝ → ℝ)
    (hΦ : sin (π * z) ^ 2 * Φ z = sin (N * (π * z)) ^ 2) (hz : sin (π * z) ≠ 0) :
    Φ z = sin (N * (π * z)) ^ 2 * (1 / sin (π * z) ^ 2) := by
  rw [← hΦ]; field_simp

private theorem sval524s (N z : ℝ) (S : ℝ → ℝ)
    (hS : sin (π * z) * S z = sin (N * (π * z)) ^ 2 * cos (π * z)
        - sin (N * (π * z)) * cos (N * (π * z)) * sin (π * z)) (hz : sin (π * z) ≠ 0) :
    S z = sin (N * (π * z)) ^ 2 * (cos (π * z) / sin (π * z))
        - sin (N * (π * z)) * cos (N * (π * z)) := by
  apply mul_left_cancel₀ hz
  rw [hS]; field_simp

private theorem algP524s (N σ P a b sc : ℝ) (hN : 0 < N) :
    1 / N ^ 2 * (σ * P) + 1 / (π * N) * ((σ * a - sc) - (σ * b - sc))
      = σ / N ^ 2 * (P - N / π * (b - a)) := by
  have := Real.pi_ne_zero
  field_simp; ring

private theorem algQ524s (N σ Q a b sc : ℝ) (hN : 0 < N) :
    1 / N ^ 2 * (N ^ 2 - σ * Q) + 1 / (π * N) * ((σ * a - sc) - (σ * b - sc))
      = 1 - σ / N ^ 2 * (Q - N / π * (a - b)) := by
  have := Real.pi_ne_zero
  field_simp; ring

private theorem ctdiff524s (a b : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0) :
    cos a / sin a - cos b / sin b = sin (b - a) / (sin a * sin b) := by
  rw [Real.sin_sub]; field_simp

private theorem sinpos524s (z : ℝ) (h0 : 0 < z) (h1 : z < 1) : 0 < sin (π * z) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
  nlinarith [Real.pi_pos]

private theorem sinneg524s (z : ℝ) (h0 : z < 0) (h1 : -1 < z) : sin (π * z) < 0 := by
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

private theorem cellPgen524s (N : ℝ) (hN : 1 ≤ N) (m : ℕ) (Φ S : ℝ → ℝ)
    (hΦ : ∀ y, sin (π * y) ^ 2 * Φ y = sin (N * (π * y)) ^ 2)
    (hS : ∀ y, sin (π * y) * S y = sin (N * (π * y)) ^ 2 * cos (π * y)
        - sin (N * (π * y)) * cos (N * (π * y)) * sin (π * y))
    (y : ℝ) (h1 : (m : ℝ) / N < y) (h2 : y < 1)
    (hs : sin (N * (π * y)) ≠ 0) :
    0 ≤ 1 / N ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / N)
        + 1 / (π * N) * (S y - S (y - (m : ℝ) / N)) := by
  have hN0 : 0 < N := by linarith
  have hNne : N ≠ 0 := hN0.ne'
  have hσ : 0 < sin (N * (π * y)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
  have hpos : ∀ j : ℕ, j ≤ m → 0 < sin (π * (y - (j : ℝ) / N)) := by
    intro j hj
    have hjm : (j : ℝ) / N ≤ (m : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hj) hN0.le
    have hj0 : 0 ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg j) hN0.le
    exact sinpos524s _ (by linarith) (by linarith)
  have hSum : ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / N)
      = sin (N * (π * y)) ^ 2 * ∑ j ∈ range (m + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [phival524s N _ Φ (hΦ _) (hpos j hj').ne', (shift524s N y hNne j).1]
  have hy0 : 0 < y := lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg m) hN0.le) h1
  have hSy : S y = sin (N * (π * y)) ^ 2 * (cos (π * y) / sin (π * y))
      - sin (N * (π * y)) * cos (N * (π * y)) :=
    sval524s N y S (hS y) (sinpos524s y hy0 h2).ne'
  have hSm : S (y - (m : ℝ) / N)
      = sin (N * (π * y)) ^ 2 * (cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N)))
      - sin (N * (π * y)) * cos (N * (π * y)) := by
    rw [sval524s N _ S (hS _) (hpos m le_rfl).ne', (shift524s N y hNne m).1,
      (shift524s N y hNne m).2]
  have T := trapezoid524s N hN y m h1 h2
  rw [hSum, hSy, hSm, algP524s _ _ _ _ _ _ hN0]
  exact mul_nonneg (div_nonneg hσ.le (sq_nonneg _)) (by linarith)

private theorem cellQgen524s (N : ℝ) (H m : ℕ) (hNH : (H : ℝ) + 1 = N) (hH : 1 ≤ H)
    (hm : m ≤ H) (Φ S : ℝ → ℝ)
    (hΦ : ∀ y, sin (π * y) ^ 2 * Φ y = sin (N * (π * y)) ^ 2)
    (hS : ∀ y, sin (π * y) * S y = sin (N * (π * y)) ^ 2 * cos (π * y)
        - sin (N * (π * y)) * cos (N * (π * y)) * sin (π * y))
    (hPU : ∀ y, ∑ j ∈ range (H + 1), Φ (y - (j : ℝ) / N) = N ^ 2)
    (y : ℝ) (h1 : 0 < y) (h2 : y < (m : ℝ) / N)
    (hs : sin (N * (π * y)) ≠ 0) :
    1 ≤ 1 / N ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / N)
        + 1 / (π * N) * (S y - S (y - (m : ℝ) / N)) := by
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hN2 : 2 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hNne : N ≠ 0 := hN0.ne'
  have hσ : 0 < sin (N * (π * y)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
  have hiN : 0 < 1 / N := one_div_pos.mpr hN0
  have hδ : 1 / (2 * N) = 1 / N / 2 := by field_simp
  have hHN : (H : ℝ) / N = 1 - 1 / N := by
    rw [← hNH]; field_simp; ring
  have hmN : (m : ℝ) / N ≤ 1 - 1 / N := by
    rw [← hHN]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hN0.le
  have hm1 : ((m + 1 : ℕ) : ℝ) / N = (m : ℝ) / N + 1 / N := by
    push_cast; ring
  have hneg : ∀ j : ℕ, m + 1 ≤ j → j ≤ H → sin (π * (y - (j : ℝ) / N)) < 0 := by
    intro j hj hjH
    have hjm : ((m + 1 : ℕ) : ℝ) / N ≤ (j : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hj) hN0.le
    have hjH' : (j : ℝ) / N ≤ (H : ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast hjH) hN0.le
    exact sinneg524s _ (by linarith) (by linarith)
  have hSum : ∑ j ∈ Ico (m + 1) (H + 1), Φ (y - (j : ℝ) / N)
      = sin (N * (π * y)) ^ 2
        * ∑ j ∈ Ico (m + 1) (H + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    rw [phival524s N _ Φ (hΦ _) (hneg j hj1 (Nat.lt_succ_iff.mp hj2)).ne,
      (shift524s N y hNne j).1]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j : ℕ => Φ (y - (j : ℝ) / N))
    (show m + 1 ≤ H + 1 by omega)
  have hR : ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / N)
      = N ^ 2 - sin (N * (π * y)) ^ 2
        * ∑ j ∈ Ico (m + 1) (H + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2 := by
    rw [← hSum, ← hPU y]; linarith
  have hsy : 0 < sin (π * y) := sinpos524s y h1 (by linarith)
  have hsm : sin (π * (y - (m : ℝ) / N)) < 0 := sinneg524s _ (by linarith) (by linarith)
  have hSy : S y = sin (N * (π * y)) ^ 2 * (cos (π * y) / sin (π * y))
      - sin (N * (π * y)) * cos (N * (π * y)) :=
    sval524s N y S (hS y) hsy.ne'
  have hSm : S (y - (m : ℝ) / N)
      = sin (N * (π * y)) ^ 2 * (cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N)))
      - sin (N * (π * y)) * cos (N * (π * y)) := by
    rw [sval524s N _ S (hS _) hsm.ne, (shift524s N y hNne m).1,
      (shift524s N y hNne m).2]
  -- midpoint
  have e1 : m + 1 + (H - m) = H + 1 := by omega
  have e2 : ((m + 1 : ℕ) : ℝ) + ((H - m : ℕ) : ℝ) = N := by
    rw [Nat.cast_sub hm, ← hNH]; push_cast; ring
  have hd0 : y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N) < 0 := by
    rw [hm1, hδ]; linarith
  have hc1 : -1 < y - N / N + 1 / (2 * N) := by
    rw [div_self hNne, hδ]; linarith
  have M := midpoint524s N hN2 y (m + 1) (H - m) hd0 (by rw [e2]; exact hc1)
  rw [e1, e2] at M
  -- cotangent comparisons
  have hc0 : y - N / N + 1 / (2 * N) < 0 := by
    rw [div_self hNne, hδ]; linarith
  have hd1 : -1 < y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N) := by
    rw [hm1, hδ]; linarith
  have hsc : sin (π * (y - N / N + 1 / (2 * N))) < 0 := sinneg524s _ hc0 hc1
  have hsd : sin (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N))) < 0 := sinneg524s _ hd0 hd1
  have I1 : cos (π * (y - N / N + 1 / (2 * N))) / sin (π * (y - N / N + 1 / (2 * N)))
      ≤ cos (π * y) / sin (π * y) := by
    have hd := ctdiff524s _ _ hsc.ne hsy.ne'
    have harg : π * y - π * (y - N / N + 1 / (2 * N)) = π * (1 - 1 / N / 2) := by
      rw [div_self hNne, hδ]; ring
    have hnum : 0 < sin (π * y - π * (y - N / N + 1 / (2 * N))) := by
      rw [harg]; exact sinpos524s _ (by linarith) (by linarith)
    have : sin (π * y - π * (y - N / N + 1 / (2 * N)))
        / (sin (π * (y - N / N + 1 / (2 * N))) * sin (π * y)) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hnum.le (mul_nonpos_of_nonpos_of_nonneg hsc.le hsy.le)
    linarith
  have I2 : cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N))
      ≤ cos (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N)))
        / sin (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N))) := by
    have hd := ctdiff524s _ _ hsm.ne hsd.ne
    have harg : π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N)) - π * (y - (m : ℝ) / N)
        = π * (-(1 / N / 2)) := by
      rw [hm1, hδ]; ring
    have hnum : sin (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N)) - π * (y - (m : ℝ) / N))
        < 0 := by
      rw [harg]; exact sinneg524s _ (by linarith) (by linarith)
    have : sin (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N)) - π * (y - (m : ℝ) / N))
        / (sin (π * (y - (m : ℝ) / N))
          * sin (π * (y - ((m + 1 : ℕ) : ℝ) / N + 1 / (2 * N)))) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum.le (mul_nonneg_of_nonpos_of_nonpos hsm.le hsd.le)
    linarith
  have hNπ : 0 ≤ N / π := div_nonneg hN0.le Real.pi_pos.le
  have M2 : ∑ j ∈ Ico (m + 1) (H + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2
      ≤ N / π * (cos (π * y) / sin (π * y)
        - cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N))) :=
    le_trans M (mul_le_mul_of_nonneg_left (by linarith) hNπ)
  rw [hR, hSy, hSm, algQ524s _ _ _ _ _ _ hN0]
  have : sin (N * (π * y)) ^ 2 / N ^ 2
      * (∑ j ∈ Ico (m + 1) (H + 1), 1 / sin (π * (y - (j : ℝ) / N)) ^ 2
        - N / π * (cos (π * y) / sin (π * y)
          - cos (π * (y - (m : ℝ) / N)) / sin (π * (y - (m : ℝ) / N)))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hσ.le (sq_nonneg _)) (by linarith)
  linarith

/-- A6a. Nonnegativity to the right of the window, off the grid. -/
private theorem cellP524s (H m : ℕ) (Φ S : ℝ → ℝ)
    (hΦ : ∀ y, sin (π * y) ^ 2 * Φ y = sin (((H : ℝ) + 1) * (π * y)) ^ 2)
    (hS : ∀ y, sin (π * y) * S y = sin (((H : ℝ) + 1) * (π * y)) ^ 2 * cos (π * y)
        - sin (((H : ℝ) + 1) * (π * y)) * cos (((H : ℝ) + 1) * (π * y)) * sin (π * y))
    (y : ℝ) (h1 : (m : ℝ) / ((H : ℝ) + 1) < y) (h2 : y < 1)
    (hs : sin (((H : ℝ) + 1) * (π * y)) ≠ 0) :
    0 ≤ 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1))
        + 1 / (π * ((H : ℝ) + 1)) * (S y - S (y - (m : ℝ) / ((H : ℝ) + 1))) := by
  exact cellPgen524s ((H : ℝ) + 1) (by have := Nat.cast_nonneg (α := ℝ) H; linarith)
    m Φ S hΦ hS y h1 h2 hs

/-- A6b. At least one inside the window, off the grid. -/
private theorem cellQ524s (H m : ℕ) (hH : 1 ≤ H) (hm : m ≤ H) (Φ S : ℝ → ℝ)
    (hΦ : ∀ y, sin (π * y) ^ 2 * Φ y = sin (((H : ℝ) + 1) * (π * y)) ^ 2)
    (hS : ∀ y, sin (π * y) * S y = sin (((H : ℝ) + 1) * (π * y)) ^ 2 * cos (π * y)
        - sin (((H : ℝ) + 1) * (π * y)) * cos (((H : ℝ) + 1) * (π * y)) * sin (π * y))
    (hPU : ∀ y, ∑ j ∈ range (H + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1)) = ((H : ℝ) + 1) ^ 2)
    (y : ℝ) (h1 : 0 < y) (h2 : y < (m : ℝ) / ((H : ℝ) + 1))
    (hs : sin (((H : ℝ) + 1) * (π * y)) ≠ 0) :
    1 ≤ 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1))
        + 1 / (π * ((H : ℝ) + 1)) * (S y - S (y - (m : ℝ) / ((H : ℝ) + 1))) := by
  exact cellQgen524s ((H : ℝ) + 1) H m rfl hH hm Φ S hΦ hS hPU y h1 h2 hs

private theorem sin_cell524s (N : ℝ) (hN : 0 < N) (k : ℕ) (z : ℝ) (h1 : (k:ℝ)/N < z)
    (h2 : z < ((k:ℝ)+1)/N) : sin (N * (π * z)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have hn' : (n:ℝ) = N * z := by
    have h3 : (n:ℝ) * π = (N*z) * π := by rw [hn]; ring
    exact mul_right_cancel₀ Real.pi_pos.ne' h3
  rw [div_lt_iff₀ hN] at h1; rw [lt_div_iff₀ hN] at h2
  have a : (k:ℝ) < n := by rw [hn']; linarith
  have b : (n:ℝ) < (k:ℝ)+1 := by rw [hn']; linarith
  have a' : (k:ℤ) < n := by exact_mod_cast a
  have b' : n < (k:ℤ)+1 := by exact_mod_cast b
  omega

/-- A7a. The majorant inequalities on the whole period, by continuity from the cells. -/
private theorem majorant_period524s (H m : ℕ) (hH : 1 ≤ H) (hm : m ≤ H) (Φ S : ℝ → ℝ)
    (hΦ : ∀ y, sin (π * y) ^ 2 * Φ y = sin (((H : ℝ) + 1) * (π * y)) ^ 2)
    (hS : ∀ y, sin (π * y) * S y = sin (((H : ℝ) + 1) * (π * y)) ^ 2 * cos (π * y)
        - sin (((H : ℝ) + 1) * (π * y)) * cos (((H : ℝ) + 1) * (π * y)) * sin (π * y))
    (hPU : ∀ y, ∑ j ∈ range (H + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1)) = ((H : ℝ) + 1) ^ 2)
    (hΦc : Continuous Φ) (hSc : Continuous S)
    (y : ℝ) (h0 : 0 ≤ y) (h1 : y < 1) :
    (0 ≤ 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1))
        + 1 / (π * ((H : ℝ) + 1)) * (S y - S (y - (m : ℝ) / ((H : ℝ) + 1))))
    ∧ (y < (m : ℝ) / ((H : ℝ) + 1) →
      1 ≤ 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1), Φ (y - (j : ℝ) / ((H : ℝ) + 1))
        + 1 / (π * ((H : ℝ) + 1)) * (S y - S (y - (m : ℝ) / ((H : ℝ) + 1)))) := by
  have hN : (0:ℝ) < (H : ℝ) + 1 := by positivity
  set U : ℝ → ℝ := fun z => 1 / ((H : ℝ) + 1) ^ 2 * ∑ j ∈ range (m + 1), Φ (z - (j : ℝ) / ((H : ℝ) + 1))
        + 1 / (π * ((H : ℝ) + 1)) * (S z - S (z - (m : ℝ) / ((H : ℝ) + 1))) with hUd
  have hU : Continuous U := by rw [hUd]; fun_prop
  have hyN : 0 ≤ y * ((H:ℝ)+1) := by positivity
  have hk1 : ((⌊y * ((H:ℝ)+1)⌋₊ : ℕ) : ℝ) ≤ y * ((H:ℝ)+1) := Nat.floor_le hyN
  have hk2 : y * ((H:ℝ)+1) < ((⌊y * ((H:ℝ)+1)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  generalize ⌊y * ((H:ℝ)+1)⌋₊ = k at hk1 hk2
  have hkH : k ≤ H := by
    have : (k:ℝ) < (H:ℝ) + 1 := by nlinarith
    have : k < H + 1 := by exact_mod_cast this
    omega
  have hya : (k:ℝ) / ((H:ℝ)+1) ≤ y := by rw [div_le_iff₀ hN]; exact hk1
  have hyb : y ≤ ((k:ℝ)+1) / ((H:ℝ)+1) := by rw [le_div_iff₀ hN]; exact hk2.le
  have hab : (k:ℝ) / ((H:ℝ)+1) < ((k:ℝ)+1) / ((H:ℝ)+1) := by
    apply div_lt_div_of_pos_right _ hN; linarith
  have hcl : ∀ c : ℝ, (∀ z ∈ Set.Ioo ((k:ℝ) / ((H:ℝ)+1)) (((k:ℝ)+1) / ((H:ℝ)+1)), c ≤ U z) → c ≤ U y := by
    intro c hc
    have hy : y ∈ closure (Set.Ioo ((k:ℝ) / ((H:ℝ)+1)) (((k:ℝ)+1) / ((H:ℝ)+1))) := by
      rw [closure_Ioo hab.ne]; exact ⟨hya, hyb⟩
    exact (isClosed_le continuous_const hU).closure_subset_iff.mpr
      (fun z hz => hc z hz) hy
  have hk0 : (0:ℝ) ≤ (k:ℝ) / ((H:ℝ)+1) := by positivity
  rcases Nat.lt_or_ge k m with hkm | hkm
  · have hle : ((k:ℝ)+1) / ((H:ℝ)+1) ≤ (m:ℝ) / ((H:ℝ)+1) := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast hkm
    have h1U : 1 ≤ U y := hcl 1 (fun z hz => by
      have hz' := Set.mem_Ioo.mp hz
      exact cellQ524s H m hH hm Φ S hΦ hS hPU z (by linarith [hz'.1]) (by linarith [hz'.2])
        (sin_cell524s _ hN k z hz'.1 hz'.2))
    exact ⟨by have : 1 ≤ U y := h1U
              linarith, fun _ => h1U⟩
  · have hle : (m:ℝ) / ((H:ℝ)+1) ≤ (k:ℝ) / ((H:ℝ)+1) := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact_mod_cast hkm
    have hle1 : ((k:ℝ)+1) / ((H:ℝ)+1) ≤ 1 := by
      rw [div_le_one hN]
      have : (k:ℝ) ≤ (H:ℝ) := by exact_mod_cast hkH
      linarith
    have h0U : 0 ≤ U y := hcl 0 (fun z hz => by
      have hz' := Set.mem_Ioo.mp hz
      exact cellP524s H m Φ S hΦ hS z (by linarith [hz'.1]) (by linarith [hz'.2])
        (sin_cell524s _ hN k z hz'.1 hz'.2))
    exact ⟨h0U, fun hlt => absurd hlt (by linarith)⟩

/-- LEAF. Existence of the majorant for the window at the origin in the wide
regime: for a width between one half and one minus the slack, and at least
four frequencies, some constant at most the width plus the slack and some
coefficients of size at most `4 / h` dominate the normalised indicator. This
is the construction of the majorant itself, where the higher frequencies have
to carry the mass that a single cosine can no longer carry at this width. -/
theorem leaf_large_width_core524 (w : ℝ) (hw1 : 1 / 2 ≤ w) (hw2 : w < 1)
    (H : ℕ) (hH : 4 ≤ H) (hC1 : w + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if Int.fract x < w then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  have hN : (0:ℝ) < (H : ℝ) + 1 := by positivity
  have hwN : 0 ≤ w * ((H:ℝ)+1) := by
    have : (0:ℝ) ≤ w := by linarith
    positivity
  have hm1 : w * ((H:ℝ)+1) ≤ ((⌈w * ((H:ℝ)+1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hm2 : ((⌈w * ((H:ℝ)+1)⌉₊ : ℕ) : ℝ) < w * ((H:ℝ)+1) + 1 := Nat.ceil_lt_add_one hwN
  generalize ⌈w * ((H:ℝ)+1)⌉₊ = m at hm1 hm2
  have hC : w * ((H:ℝ)+1) + 4 < (H:ℝ)+1 := by
    have := mul_lt_mul_of_pos_right hC1 hN
    rwa [add_mul, div_mul_cancel₀ _ hN.ne', one_mul] at this
  have hmH : m ≤ H := by
    have : (m:ℝ) < (H:ℝ) + 1 := by linarith
    have : m < H + 1 := by exact_mod_cast this
    omega
  have hwm : w ≤ (m:ℝ) / ((H:ℝ)+1) := by rw [le_div_iff₀ hN]; exact hm1
  refine ⟨((m : ℝ) + 1) / ((H : ℝ) + 1), fun h =>
      (((2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ)) : ℝ)) : ℂ)
          * ∑ j ∈ range (m + 1), eC (-((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
          * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1))))), ?_, ?_, ?_⟩
  · have e : w + 4 / ((H:ℝ)+1) = (w * ((H:ℝ)+1) + 4) / ((H:ℝ)+1) := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hN.le
    linarith
  · intro h hh
    have hh' := Finset.mem_Icc.mp hh
    exact coeff_bound524s H m h hh'.1 hh'.2
  · intro x
    have hper := periodic524s H (fun h =>
      (((2 / ((H : ℝ) + 1) ^ 2 * (((H : ℝ) + 1) - (h : ℝ)) : ℝ)) : ℂ)
          * ∑ j ∈ range (m + 1), eC (-((h : ℝ) * ((j : ℝ) / ((H : ℝ) + 1))))
        + (((1 / (π * ((H : ℝ) + 1)) : ℝ)) : ℂ) * (-Complex.I)
          * (1 - eC (-((h : ℝ) * ((m : ℝ) / ((H : ℝ) + 1)))))) x
    have hmaj := majorant_period524s H m (by omega) hmH
      (fun y => ((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H,
            (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * (h : ℝ) * y))
      (fun y => ∑ h ∈ Icc 1 H, sin (2 * π * (h : ℝ) * y))
      (fejer524s H) (conj524s H) (partition524s H) (by fun_prop) (by fun_prop)
      (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
    beta_reduce at hper hmaj ⊢
    rw [hper, realpart524s H m (Int.fract x)]
    obtain ⟨p0, p1⟩ := hmaj
    split_ifs with hlt
    · exact p1 (lt_of_lt_of_le hlt hwm)
    · exact p0

/-- The target of the parent file in the wide regime, assembled from the
normalisation of the window and the existence of a majorant for the window at
the origin. -/
theorem leaf_majorant_large_width524_split (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : 1 / 2 ≤ b - a)
    (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  have hden : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hwidth : b - a < 1 := by
    have hpos : (0 : ℝ) < 4 / ((H : ℝ) + 1) := by positivity
    linarith
  exact leaf_large_width_shift524 a b hab ha hb H
    (leaf_large_width_core524 (b - a) hw1 hwidth H hH hC1)

/-! ### The critical-grid device for the complex form

The sibling leaves of `SPLIT_leaf_majorant_small_width524` are refuted by sampling the
majorant at the `H + 1` points `j / (H + 1)`. There the majorant is built from the real
cosines alone, so it is *even*, and the sampled values are at least one on the mirror block
as well; the identity `∑_j g (j / N) = N c₀` then forces `c₀ ≥ 2 w - 1 / N`, which the
budget `w + 4 / N` cannot meet once `w (H + 1) > 5`.

This file's leaf is in the complex form `Re ∑ c h · e (h x)`, which is not even, so only the
block inside the window is forced: the same device gives `c₀ ≥ (m + 1) / N` for the largest
`m` with `m / N < w`, i.e. `c₀ ≥ w - 1 / N`. That is compatible with the budget `w + 4 / N`
for every `H`, so the device that killed the even form does not refute this leaf. The two
lemmas below are exactly that statement, and the pair at the end exhibits it at the first
admissible parameters. -/

/-- **The critical-grid mean identity, complex form.** The mean of a complex-exponential
polynomial of degree at most `H` is recovered exactly as the average of its values at the
`H + 1` points `j / (H + 1)`. -/
private theorem grid_mean_complex524 (H : ℕ) (c₀ : ℝ) (c : ℕ → ℂ) :
    (∑ j ∈ Finset.range (H + 1), (c₀ + (∑ h ∈ Finset.Icc 1 H,
        c h * eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ)))).re))
      = (((H + 1 : ℕ)) : ℝ) * c₀ := by
  have hstep : ∀ j : ℕ, (c₀ + (∑ h ∈ Finset.Icc 1 H,
        c h * eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ)))).re)
      = c₀ + ∑ h ∈ Finset.Icc 1 H,
          (c h * eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ)))).re := by
    intro j
    rw [Complex.re_sum]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib]
  have hzero : (∑ j ∈ Finset.range (H + 1), ∑ h ∈ Finset.Icc 1 H,
      (c h * eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ)))).re) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero ?_
    intro h hh
    have h1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
    have h2 : h ≤ (H + 1) - 1 := by
      have := (Finset.mem_Icc.mp hh).2
      omega
    have hkey : (∑ j ∈ Finset.range (H + 1),
        (c h * eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ)))).re)
        = (c h * (∑ j ∈ Finset.range (H + 1),
            eC ((h : ℝ) * ((j : ℝ) / (((H + 1 : ℕ)) : ℝ))))).re := by
      rw [Finset.mul_sum, Complex.re_sum]
    rw [hkey, eC_grid_sum524c h (H + 1) h1 h2, mul_zero, Complex.zero_re]
  rw [hzero, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The obstruction, abstractly, in the complex form.** A `g` that dominates
`1_[0,w)` and whose values at the critical grid sum to `N c₀` has `(m + 1) ≤ N c₀` for every
`m < N` with `m / N < w`. Note the single block: no mirror block, hence no contradiction
with the budget `w + 4 / N`. -/
private theorem grid_bound_complex524 (w : ℝ) (N m : ℕ) (hmN : m < N)
    (hmw : (m : ℝ) / N < w) (g : ℝ → ℝ) (c₀ : ℝ)
    (hdom : ∀ x : ℝ, (if Int.fract x < w then (1 : ℝ) else 0) ≤ g x)
    (hgrid : (∑ j ∈ Finset.range N, g ((j : ℝ) / N)) = (N : ℝ) * c₀) :
    ((m : ℝ) + 1) ≤ (N : ℝ) * c₀ := by
  classical
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    have h := hdom x
    split_ifs at h with hx
    · linarith
    · linarith
  have hpt1 : ∀ j : ℕ, j ≤ m → 1 ≤ g ((j : ℝ) / N) := by
    intro j hj
    have hj' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
    have hjw : (j : ℝ) / N < w := by
      calc (j : ℝ) / N ≤ (m : ℝ) / N := by gcongr
        _ < w := hmw
    have hj1 : (j : ℝ) / N < 1 := by
      rw [div_lt_one hNR]
      exact_mod_cast (lt_of_le_of_lt hj hmN)
    have hfr : Int.fract ((j : ℝ) / N) = (j : ℝ) / N :=
      Int.fract_eq_self.mpr ⟨by positivity, hj1⟩
    have h := hdom ((j : ℝ) / N)
    rwa [hfr, if_pos hjw] at h
  have hlow : ((m : ℝ) + 1) ≤ ∑ j ∈ Finset.range (m + 1), g ((j : ℝ) / N) := by
    have h1 : (∑ _j ∈ Finset.range (m + 1), (1 : ℝ))
        ≤ ∑ j ∈ Finset.range (m + 1), g ((j : ℝ) / N) :=
      Finset.sum_le_sum (fun j hj => hpt1 j (by have := Finset.mem_range.mp hj; omega))
    have hsum : (∑ _j ∈ Finset.range (m + 1), (1 : ℝ)) = ((m : ℝ) + 1) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      ring
    linarith [h1, hsum]
  have hle : (∑ j ∈ Finset.range (m + 1), g ((j : ℝ) / N))
      ≤ ∑ j ∈ Finset.range N, g ((j : ℝ) / N) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
      (fun x _ _ => hg_nonneg ((x : ℝ) / N))
  linarith [hlow, hle, hgrid]

/-- At `w = 1 / 2` and `H = 8` the grid device forces only `c₀ ≥ 5 / 9`, against the budget
`1 / 2 + 4 / 9 = 17 / 18`: the complex-form leaf survives the argument that refutes its
even-form siblings. -/
theorem large524_grid_lower_half (c₀ : ℝ) (c : ℕ → ℂ)
    (hdom : ∀ x : ℝ, (if Int.fract x < 1 / 2 then (1 : ℝ) else 0) ≤
      c₀ + (∑ h ∈ Finset.Icc 1 8, c h * eC ((h : ℝ) * x)).re) :
    (5 : ℝ) / 9 ≤ c₀ := by
  have hgrid := grid_mean_complex524 8 c₀ c
  have hb := grid_bound_complex524 (1 / 2) 9 4 (by norm_num) (by norm_num)
    (fun x => c₀ + (∑ h ∈ Finset.Icc 1 8, c h * eC ((h : ℝ) * x)).re) c₀ hdom hgrid
  norm_num at hb
  linarith

/-- The two numbers of the previous lemma: the forced lower bound `5 / 9` is strictly below
the budget `17 / 18`, so no contradiction arises. -/
theorem large524_grid_no_contradiction :
    (5 : ℝ) / 9 < (1 / 2 : ℝ) + 4 / ((8 : ℝ) + 1) := by
  norm_num

/-- The hypotheses of `leaf_large_width_core524` force `8 ≤ H`: with `H ≤ 7` the hypothesis
`w + 4 / (H + 1) < 1` and `1 / 2 ≤ w` are contradictory, so `hH : 4 ≤ H` is not the binding
lower bound and the leaf is vacuous there. -/
private theorem core524_forces_eight (w : ℝ) (H : ℕ) (hw1 : 1 / 2 ≤ w)
    (hC1 : w + 4 / ((H : ℝ) + 1) < 1) : 8 ≤ H := by
  have hpos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have h2 : 4 / ((H : ℝ) + 1) < 1 / 2 := by linarith
  have h3 : (4 : ℝ) < (1 / 2) * ((H : ℝ) + 1) := by
    have h := (div_lt_iff₀ hpos).mp h2
    linarith
  have h4 : (7 : ℝ) < (H : ℝ) := by linarith
  have h5 : 7 < H := by exact_mod_cast h4
  omega

end LeanLab.ExceptionalSet.Decomp524a
