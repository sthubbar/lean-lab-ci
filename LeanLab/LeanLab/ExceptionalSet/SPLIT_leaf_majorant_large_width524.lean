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
  sorry

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
