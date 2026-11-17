import LeanLab.ExceptionalSet.SPLIT_leaf_interval_majorant524

/-!
Split of `LeanLab.ExceptionalSet.Decomp524a.leaf_majorant_mid_width524`, the
width-`1/3`-to-`1/2` regime of the finite Fourier majorant for the indicator of
an interval of fractional parts.

In this regime the cosine of the half-width is still positive, but a single
cosine centred at the midpoint would need an amplitude larger than the constant
allows, so the majorant has to carry mass on the higher frequencies.  The three
leaves below are that construction, stated for the interval centred at the
origin (translating by the midpoint and folding modulo one is what the assembly
does) and with real cosine coefficients (the phase `e(-h m)` of the target is
what the assembly puts into the complex coefficients).

Each leaf covers one sub-range of the width: `1 / 3 < w ≤ 7 / 20`,
`7 / 20 < w ≤ 9 / 20`, and `9 / 20 < w < 1 / 2`.

`leaf_majorant_mid_width524_split` proves the target from the leaves with no
`sorry` of its own and without using the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-! ### Leaves -/

/-- LEAF. The low part of the intermediate width range, `1 / 3 < w ≤ 7 / 20`: there are a
constant `c₀ ≤ w + 4 / (H + 1)` and real coefficients `g h` with `|g h| ≤ 4 / h` for
`1 ≤ h ≤ H` such that `c₀ + ∑ h, g h cos (2 π h θ)` dominates the indicator of the centred
interval `[-w/2, w/2]` at every real `θ`.  This is the construction step: the coefficients are
built here, and the assembly only translates them back to an arbitrary interval. -/
theorem leaf_cosine_majorant_low_width524 (w : ℝ) (H : ℕ) (hw1 : 1 / 3 < w)
    (hw2 : w ≤ 7 / 20) (hH : 4 ≤ H) (hC : w + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ g : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      ∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ)) := by
  sorry

/-- LEAF. The middle part of the intermediate width range, `7 / 20 < w ≤ 9 / 20`: the same
centred construction, with the constant `c₀ ≤ w + 4 / (H + 1)` and coefficients `|g h| ≤ 4 / h`
for `1 ≤ h ≤ H`.  Here the half-width is closer to a quarter, so the single-cosine term that
the parent uses in the narrow regime no longer fits under the constant and the mass on the
higher frequencies carries more of the interval. -/
theorem leaf_cosine_majorant_mid_width524 (w : ℝ) (H : ℕ) (hw1 : 7 / 20 < w)
    (hw2 : w ≤ 9 / 20) (hH : 4 ≤ H) (hC : w + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ g : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      ∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ)) := by
  sorry

/-- LEAF. The high part of the intermediate width range, `9 / 20 < w < 1 / 2`: the same
centred construction, with the constant `c₀ ≤ w + 4 / (H + 1)` and coefficients `|g h| ≤ 4 / h`
for `1 ≤ h ≤ H`.  This is the widest case of the regime, where `w / 2` is close to a quarter
and the majorant has the least room off the interval. -/
theorem leaf_cosine_majorant_high_width524 (w : ℝ) (H : ℕ) (hw1 : 9 / 20 < w)
    (hw2 : w < 1 / 2) (hH : 4 ≤ H) (hC : w + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ g : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      ∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ)) := by
  sorry

/-! ### Elementary facts about `eC`, proved -/

/-- `eC t` is the exponential of a real multiple of `I`. -/
private theorem eC_def524 (t : ℝ) :
    eC t = Complex.exp ((2 * π * t : ℝ) * Complex.I) := by
  unfold eC
  congr 1
  push_cast
  ring

/-- The real part of `eC t` is `cos (2 π t)`. -/
private theorem eC_re524 (t : ℝ) : (eC t).re = cos (2 * π * t) := by
  rw [eC_def524, Complex.exp_ofReal_mul_I_re]

/-- `eC` has modulus one. -/
private theorem eC_norm524 (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC_def524, Complex.norm_exp_ofReal_mul_I]

/-- `eC` is multiplicative. -/
private theorem eC_mul524 (s t : ℝ) : eC s * eC t = eC (s + t) := by
  simp only [eC_def524, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The translation from the centred leaves to an arbitrary interval, proved -/

/-- The real part of a finite sum of complex numbers is the sum of the real parts. -/
private theorem re_sum524 (s : Finset ℕ) (z : ℕ → ℂ) :
    (∑ h ∈ s, z h).re = ∑ h ∈ s, (z h).re := by
  rw [← Complex.reCLM_apply, map_sum]
  exact (Finset.sum_congr rfl fun h _ => (Complex.reCLM_apply (z h)).symm)

/-- A centred cosine majorant of the indicator of `[-w/2, w/2]`, with `w` the width of
`[a, b)`, gives the target conclusion for `[a, b)`: the midpoint `(a + b) / 2` is folded
into the coefficients as the phase `e (-h m)`, and the argument `Int.fract x - (a + b) / 2`
is compared with `Int.fract x` through `cos (u + n (2 π)) = cos u`. -/
private theorem centred_to_target524 (a b w : ℝ) (H : ℕ) (c₀ : ℝ) (g : ℕ → ℝ)
    (hw : w = b - a)
    (hpt : ∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
      c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ))) :
    ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
      c₀ + (∑ h ∈ Icc 1 H, ((g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2)))) *
        eC ((h : ℝ) * x)).re := by
  intro x
  have hind : (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
      (if |Int.fract x - (a + b) / 2| ≤ w / 2 then (1 : ℝ) else 0) := by
    by_cases hx : a ≤ Int.fract x ∧ Int.fract x < b
    · have habs : |Int.fract x - (a + b) / 2| ≤ w / 2 := by
        rw [abs_le, hw]
        constructor <;> linarith [hx.1, hx.2]
      rw [if_pos hx, if_pos habs]
    · rw [if_neg hx]
      split_ifs <;> norm_num
  have hsum : (∑ h ∈ Icc 1 H,
        ((g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2))) * eC ((h : ℝ) * x)).re)
      = ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * (Int.fract x - (a + b) / 2))) := by
    refine Finset.sum_congr rfl fun h _ => ?_
    have hstep : (g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2))) * eC ((h : ℝ) * x)
        = (g h : ℂ) * eC ((h : ℝ) * x - (h : ℝ) * ((a + b) / 2)) := by
      rw [mul_assoc, eC_mul524]
      congr 1
      ring
    have hfl : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
    have hdm : x - (a + b) / 2 = (Int.fract x - (a + b) / 2) + (⌊x⌋ : ℝ) := by
      linarith
    have harg : 2 * π * ((h : ℝ) * x - (h : ℝ) * ((a + b) / 2))
        = 2 * π * ((h : ℝ) * (Int.fract x - (a + b) / 2))
          + (((⌊x⌋ : ℤ) * (h : ℤ) : ℤ) : ℝ) * (2 * π) := by
      have h1 : (h : ℝ) * x - (h : ℝ) * ((a + b) / 2)
          = (h : ℝ) * (x - (a + b) / 2) := by ring
      rw [h1, hdm]
      push_cast
      ring
    rw [hstep, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      eC_re524, harg, Real.cos_add_int_mul_two_pi]
  calc (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0)
      ≤ (if |Int.fract x - (a + b) / 2| ≤ w / 2 then (1 : ℝ) else 0) := hind
    _ ≤ c₀ + ∑ h ∈ Icc 1 H,
          g h * cos (2 * π * ((h : ℝ) * (Int.fract x - (a + b) / 2))) := hpt _
    _ = c₀ + (∑ h ∈ Icc 1 H,
          ((g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2))) * eC ((h : ℝ) * x))).re := by
        rw [re_sum524, hsum]

/-! ### Assembly -/

set_option maxHeartbeats 1000000 in
/-- The target of the parent file in the intermediate width regime, proved from the three
width leaves above: pick the leaf whose width sub-range contains `b - a`, then translate its
centred majorant to `[a, b)`. -/
theorem leaf_majorant_mid_width524_split (a b : ℝ) (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (H : ℕ) (hH : 4 ≤ H) (hw1 : 1 / 3 < b - a)
    (hw2 : b - a < 1 / 2) (hC1 : b - a + 4 / ((H : ℝ) + 1) < 1) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  classical
  set w : ℝ := b - a with hw
  have hw13 : 1 / 3 < w := by rw [hw]; linarith
  have hw12 : w < 1 / 2 := by rw [hw]; linarith
  have hCw : w + 4 / ((H : ℝ) + 1) < 1 := by rw [hw]; linarith
  obtain ⟨c₀, g, hc₀, hg, hpt⟩ : ∃ c₀ : ℝ, ∃ g : ℕ → ℝ,
      c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, |g h| ≤ 4 / (h : ℝ)) ∧
      (∀ θ : ℝ, (if |θ| ≤ w / 2 then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Icc 1 H, g h * cos (2 * π * ((h : ℝ) * θ))) := by
    rcases le_or_gt w (7 / 20) with h7 | h7
    · obtain ⟨c₀, g, h1, h2, h3⟩ := leaf_cosine_majorant_low_width524 w H hw13 h7 hH hCw
      exact ⟨c₀, g, h1, h2, h3⟩
    · rcases le_or_gt w (9 / 20) with h9 | h9
      · obtain ⟨c₀, g, h1, h2, h3⟩ := leaf_cosine_majorant_mid_width524 w H h7 h9 hH hCw
        exact ⟨c₀, g, h1, h2, h3⟩
      · obtain ⟨c₀, g, h1, h2, h3⟩ := leaf_cosine_majorant_high_width524 w H h9 hw12 hH hCw
        exact ⟨c₀, g, h1, h2, h3⟩
  refine ⟨c₀, fun h => (g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2))), ?_, ?_, ?_⟩
  · exact hc₀
  · intro h hh
    have h1 : ‖(g h : ℂ) * eC (-((h : ℝ) * ((a + b) / 2)))‖ = |g h| := by
      rw [norm_mul, eC_norm524, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h1]
    exact hg h hh
  · exact centred_to_target524 a b w H c₀ g hw hpt

end LeanLab.ExceptionalSet.Decomp524a
