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
indicator rather than a bump: the finite Fourier majorant of Lemma 4 in the
wide width regime. -/
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
