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

end LeanLab.ExceptionalSet.Decomp524a
