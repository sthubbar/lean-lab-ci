import LeanLab.Halupczok2012.Split398aMajorA7

/-!
Tools for leaf `Split398aMajorA7.e2_twisted_partial_summation`, PP1993 page 46 display 12.
Source: A. Perelli and J. Pintz, J. London Math. Soc. 47, 1993, pages 41 to 49, PP1993.
The paper bounds the twisted sum of Lambda chi minus delta_chi against e of n eta by partial
summation: the sum is at most the largest initial segment sum times 1 plus the total variation
of e of n eta, and the variation of e between consecutive n is at most 2 pi |eta|.
Proved here: `phase_sub_norm_le`, the Lipschitz bound for e; `phase_step_norm_le`, its
consecutive step form; `phase_variation_le`, the total variation over m steps; and `abel_bound`, the discrete partial summation inequality.
Round 3 adds the kRange shift `kRange_eq_image`, `sum_kRange_eq_range`, the counts
`kRange_count_le` and `kRange_count_ge`, `count_eta_le`, `twisted_kRange_le`,
`initial_eq_full_sub_tail`, `segments_le`, `term_norm_le`, `sum_sub_const_close` and
`short_segment_le`.
The leaf e2 itself is not closed in this file.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Split398aMajorE2

open Finset
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp398a

/-- Proved: e is 2 pi Lipschitz, the norm of e x minus e y is at most 2 pi |x - y|. -/
theorem phase_sub_norm_le (x y : ℝ) : ‖phase x - phase y‖ ≤ 2 * Real.pi * |x - y| := by
  have hx : phase x = phase y * phase (x - y) := by
    unfold phase
    rw [← LeanLab.PNTPort.LargeSieve.e_add]; congr 1; ring
  rw [hx, show phase y * phase (x - y) - phase y = phase y * (phase (x - y) - 1) by ring,
    norm_mul]
  unfold phase
  rw [LeanLab.PNTPort.LargeSieve.norm_e, one_mul]
  unfold LeanLab.PNTPort.LargeSieve.e
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

/-- Proved: the variation of e of n eta between n and n + 1 is at most 2 pi |eta|. -/
theorem phase_step_norm_le (n : ℕ) (η : ℝ) :
    ‖phase (((n + 1 : ℕ) : ℝ) * η) - phase ((n : ℝ) * η)‖ ≤ 2 * Real.pi * |η| := by
  refine (phase_sub_norm_le _ _).trans (le_of_eq ?_)
  congr 2; push_cast; ring

/-- Proved: discrete partial summation. If every initial sum of a is at most M in norm, then
the sum of a i b i over i below m is at most M times the last weight plus the total variation
of b. -/
theorem abel_bound (a b : ℕ → ℂ) (m : ℕ) (M : ℝ)
    (hA : ∀ k, k ≤ m → ‖∑ i ∈ range k, a i‖ ≤ M) :
    ‖∑ i ∈ range m, a i * b i‖ ≤
      M * (‖b (m - 1)‖ + ∑ i ∈ range (m - 1), ‖b (i + 1) - b i‖) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have h := Finset.sum_range_by_parts b a m
  simp only [smul_eq_mul] at h
  rw [show ∑ i ∈ range m, a i * b i = ∑ i ∈ range m, b i * a i from
    sum_congr rfl fun i _ => mul_comm _ _, h]
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hA m le_rfl) (norm_nonneg _)
  · refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [norm_mul, mul_comm]
    have hi' : i + 1 ≤ m := by have := mem_range.mp hi; omega
    exact mul_le_mul_of_nonneg_right (hA (i + 1) hi') (norm_nonneg _)

/-- Proved: the total variation of e of n eta over m consecutive n starting at s is at most
m times 2 pi |eta|, the factor that partial summation costs in display 12. -/
theorem phase_variation_le (s m : ℕ) (η : ℝ) :
    ∑ i ∈ range m, ‖phase (((s + i + 1 : ℕ) : ℝ) * η) - phase (((s + i : ℕ) : ℝ) * η)‖ ≤
      m * (2 * Real.pi * |η|) := by
  calc _ ≤ ∑ _i ∈ range m, 2 * Real.pi * |η| :=
        sum_le_sum fun i _ => phase_step_norm_le (s + i) η
    _ = m * (2 * Real.pi * |η|) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Proved: for X and R nonnegative, kRange X R is the image of range of floor of X + R minus
floor of X under i maps to floor X + 1 + i, the shifted range form needed for display 12. -/
theorem kRange_eq_image (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) :
    kRange X R = (range (⌊X + R⌋₊ - ⌊X⌋₊)).image (fun i => ⌊X⌋₊ + 1 + i) := by
  ext k
  have hXR : 0 ≤ X + R := by linarith
  simp only [kRange, mem_filter, mem_Icc, mem_image, mem_range]
  constructor
  · rintro ⟨⟨-, -⟩, h1, h2⟩
    have a1 : ⌊X⌋₊ < k := (Nat.floor_lt hX).mpr h1
    have a2 : k ≤ ⌊X + R⌋₊ := (Nat.le_floor_iff hXR).mpr h2
    exact ⟨k - ⌊X⌋₊ - 1, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    have a1 : ⌊X⌋₊ < ⌊X⌋₊ + 1 + i := by omega
    have a2 : ⌊X⌋₊ + 1 + i ≤ ⌊X + R⌋₊ := by omega
    have b1 := (Nat.floor_lt hX).mp a1
    have b2 := (Nat.le_floor_iff hXR).mp a2
    refine ⟨⟨Nat.zero_le _, ?_⟩, b1, b2⟩
    exact_mod_cast b2.trans (Nat.le_ceil _)

/-- Proved: a sum over kRange X R, X and R nonnegative, is the shifted range sum over i below
floor of X + R minus floor of X of the term at floor X + 1 + i. -/
theorem sum_kRange_eq_range (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) (f : ℕ → ℂ) :
    ∑ n ∈ kRange X R, f n = ∑ i ∈ range (⌊X + R⌋₊ - ⌊X⌋₊), f (⌊X⌋₊ + 1 + i) := by
  rw [kRange_eq_image X R hX hR, sum_image]
  intro i _ j _ h
  simpa using h

/-- Proved: the number of terms of kRange X R, X and R nonnegative, is at most R + 1. -/
theorem kRange_count_le (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) :
    ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) ≤ R + 1 := by
  have h1 : (⌊X + R⌋₊ : ℝ) ≤ X + R := Nat.floor_le (by linarith)
  have h2 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have h3 : ⌊X⌋₊ ≤ ⌊X + R⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub h3]
  linarith

/-- Proved: for eta in xi'_q and Y at least 1, the count Y + 1 of terms times |eta| is at
most 2 L^{2B} over q, the factor partial summation costs in display 12. -/
theorem count_eta_le (N Y ε A η : ℝ) (q : ℕ) (hq : 1 ≤ q) (hY : 1 ≤ Y)
    (hη : η ∈ LeanLab.Halupczok2012.Split398aMajor.xiArc N Y ε A q) :
    (Y + 1) * |η| ≤ 2 * (Real.log N ^ (2 * LeanLab.Halupczok2012.Split398aMajor.bigB ε A) / q) := by
  simp only [LeanLab.Halupczok2012.Split398aMajor.xiArc, Set.mem_Ioo] at hη
  have habs : |η| < LeanLab.Halupczok2012.Split398aMajor.arcWidth N Y ε A q := abs_lt.mpr hη
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hYp : 0 < Y := by linarith
  have hw : LeanLab.Halupczok2012.Split398aMajor.arcWidth N Y ε A q * Y =
      Real.log N ^ (2 * LeanLab.Halupczok2012.Split398aMajor.bigB ε A) / q := by
    unfold LeanLab.Halupczok2012.Split398aMajor.arcWidth
    field_simp
  rw [← hw]
  calc (Y + 1) * |η| ≤ (2 * Y) * |η| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ ≤ (2 * Y) * LeanLab.Halupczok2012.Split398aMajor.arcWidth N Y ε A q :=
        mul_le_mul_of_nonneg_left habs.le (by linarith)
    _ = 2 * (LeanLab.Halupczok2012.Split398aMajor.arcWidth N Y ε A q * Y) := by ring

/-- Proved: partial summation over kRange X R. If every initial segment sum of a over the
shifted range is at most M in norm, then the sum of a n e of n eta over kRange X R is at most
M times 1 plus R + 1 times 2 pi |eta|, the display 12 reduction to initial segments. -/
theorem twisted_kRange_le (X R η M : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) (a : ℕ → ℂ)
    (hA : ∀ k, k ≤ ⌊X + R⌋₊ - ⌊X⌋₊ → ‖∑ i ∈ range k, a (⌊X⌋₊ + 1 + i)‖ ≤ M) :
    ‖∑ n ∈ kRange X R, a n * phase ((n : ℝ) * η)‖ ≤
      M * (1 + (R + 1) * (2 * Real.pi * |η|)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  rw [sum_kRange_eq_range X R hX hR (fun n => a n * phase ((n : ℝ) * η))]
  set m := ⌊X + R⌋₊ - ⌊X⌋₊ with hm
  set s := ⌊X⌋₊ + 1 with hs
  have key := abel_bound (fun i => a (s + i)) (fun i => phase (((s + i : ℕ) : ℝ) * η)) m M hA
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hM)
  have h1 : ‖phase (((s + (m - 1) : ℕ) : ℝ) * η)‖ = 1 := by
    unfold phase; exact LeanLab.PNTPort.LargeSieve.norm_e _
  have h2 := phase_variation_le s (m - 1) η
  have h3 : ((m - 1 : ℕ) : ℝ) ≤ R + 1 := by
    have := kRange_count_le X R hX hR
    rw [← hm] at this
    have : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    linarith
  have h4 : 0 ≤ 2 * Real.pi * |η| := by positivity
  rw [h1]
  have h5 : ∑ i ∈ range (m - 1), ‖phase (((s + (i + 1) : ℕ) : ℝ) * η) -
      phase (((s + i : ℕ) : ℝ) * η)‖ ≤ ((m - 1 : ℕ) : ℝ) * (2 * Real.pi * |η|) := by
    simpa only [add_assoc] using h2
  have h6 := mul_le_mul_of_nonneg_right h3 h4
  linarith

/-- Proved: an initial segment of the shifted range is the full kRange sum minus a tail, and
the tail is again a kRange sum, over t below n at most X + R with t = floor X + k. This lets
ShortSW, stated for intervals ending at N, bound every initial segment in display 12. -/
theorem initial_eq_full_sub_tail (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) (f : ℕ → ℂ) (k : ℕ)
    (hk : k ≤ ⌊X + R⌋₊ - ⌊X⌋₊) :
    ∑ i ∈ range k, f (⌊X⌋₊ + 1 + i) =
      ∑ n ∈ kRange X R, f n -
        ∑ n ∈ kRange ((⌊X⌋₊ + k : ℕ) : ℝ) (X + R - ((⌊X⌋₊ + k : ℕ) : ℝ)), f n := by
  have hXR : 0 ≤ X + R := by linarith
  have hfl : ⌊X⌋₊ ≤ ⌊X + R⌋₊ := Nat.floor_le_floor (by linarith)
  have ht : ⌊X⌋₊ + k ≤ ⌊X + R⌋₊ := by omega
  have htR : ((⌊X⌋₊ + k : ℕ) : ℝ) ≤ X + R :=
    (Nat.cast_le.mpr ht).trans (Nat.floor_le hXR)
  rw [sum_kRange_eq_range X R hX hR,
    sum_kRange_eq_range _ _ (Nat.cast_nonneg _) (by linarith)]
  rw [Nat.floor_natCast, show ((⌊X⌋₊ + k : ℕ) : ℝ) + (X + R - ((⌊X⌋₊ + k : ℕ) : ℝ)) = X + R
    by ring]
  have hsplit : ⌊X + R⌋₊ - ⌊X⌋₊ = k + (⌊X + R⌋₊ - (⌊X⌋₊ + k)) := by omega
  rw [hsplit, sum_range_add]
  have : ∀ j, ⌊X⌋₊ + 1 + (k + j) = ⌊X⌋₊ + k + 1 + j := fun j => by omega
  simp only [this]
  ring

/-- Proved: the trivial bound for one term of display 12, the norm of Lambda n chi n minus
delta_chi is at most log n + 1. -/
theorem term_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
        LeanLab.Halupczok2012.Split398aMajor.deltaChi χ‖ ≤ Real.log n + 1 := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
    have h2 : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ Real.log n := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log
    have h3 : 0 ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · exact Real.log_nonneg (by exact_mod_cast h)
    nlinarith [norm_nonneg ((ArithmeticFunction.vonMangoldt n : ℂ)), norm_nonneg (χ (n : ZMod q))]
  · unfold LeanLab.Halupczok2012.Split398aMajor.deltaChi
    split_ifs <;> simp

/-- Proved: the number of terms of kRange X R, X and R nonnegative, is at least R - 1. -/
theorem kRange_count_ge (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) :
    R - 1 ≤ ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) := by
  have h1 : X + R < (⌊X + R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX
  have h3 : ⌊X⌋₊ ≤ ⌊X + R⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub h3]
  linarith

/-- Proved: subtracting a constant d of norm at most 1 from each term of a kRange sum differs
from subtracting d R by at most 1 in norm, so ShortSW, stated with delta_chi Y, bounds the
sum of Lambda chi minus delta_chi up to 1. -/
theorem sum_sub_const_close (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) (f : ℕ → ℂ) (d : ℂ)
    (hd : ‖d‖ ≤ 1) :
    ‖∑ n ∈ kRange X R, (f n - d) - ((∑ n ∈ kRange X R, f n) - d * (R : ℂ))‖ ≤ 1 := by
  have hc : (kRange X R).card = ⌊X + R⌋₊ - ⌊X⌋₊ := by
    rw [kRange_eq_image X R hX hR, card_image_of_injective _ (fun i j h => by simpa using h),
      card_range]
  rw [sum_sub_distrib, sum_const, hc, nsmul_eq_mul]
  have : (∑ n ∈ kRange X R, f n) - ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℂ) * d -
      ((∑ n ∈ kRange X R, f n) - d * (R : ℂ)) =
      d * ((R : ℂ) - ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℂ)) := by ring
  rw [this, norm_mul]
  have h1 := kRange_count_le X R hX hR
  have h2 := kRange_count_ge X R hX hR
  have h3 : ‖(R : ℂ) - ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℂ)‖ ≤ 1 := by
    rw [show (R : ℂ) - ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℂ) =
      ((R - ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖d‖ * _ ≤ 1 * 1 := mul_le_mul hd h3 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Proved: the trivial bound for a short segment in display 12, the sum of Lambda chi minus
delta_chi over kRange X R is at most R + 1 times log of X + R plus 1, for X + R at least 1. -/
theorem short_segment_le {q : ℕ} (χ : DirichletCharacter ℂ q) (X R : ℝ) (hX : 0 ≤ X)
    (hR : 0 ≤ R) (hXR1 : 1 ≤ X + R) :
    ‖∑ n ∈ kRange X R, ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
        LeanLab.Halupczok2012.Split398aMajor.deltaChi χ)‖ ≤
      (R + 1) * (Real.log (X + R) + 1) := by
  have hc : (kRange X R).card = ⌊X + R⌋₊ - ⌊X⌋₊ := by
    rw [kRange_eq_image X R hX hR, card_image_of_injective _ (fun i j h => by simpa using h),
      card_range]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ n ∈ kRange X R, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) -
        LeanLab.Halupczok2012.Split398aMajor.deltaChi χ‖ ≤ Real.log (X + R) + 1 := by
    intro n hn
    simp only [kRange, mem_filter] at hn
    obtain ⟨-, h1, h2⟩ := hn
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt hX h1
    refine (term_norm_le χ n).trans ?_
    have := Real.log_le_log hn0 h2
    linarith
  have hlog : 0 ≤ Real.log (X + R) + 1 := by
    have := Real.log_nonneg hXR1; linarith
  calc ∑ n ∈ kRange X R, _ ≤ ∑ _n ∈ kRange X R, (Real.log (X + R) + 1) := sum_le_sum hb
    _ = ((⌊X + R⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) * (Real.log (X + R) + 1) := by
        rw [sum_const, hc, nsmul_eq_mul]
    _ ≤ (R + 1) * (Real.log (X + R) + 1) :=
        mul_le_mul_of_nonneg_right (kRange_count_le X R hX hR) hlog

/-- Proved: if the full kRange sum and every tail sum over t below n at most X + R, t a natural
number from floor X to floor of X + R, are at most M in norm, then every initial segment of the
shifted range is at most 2 M, the hypothesis of `twisted_kRange_le`. -/
theorem segments_le (X R M : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) (f : ℕ → ℂ)
    (hF : ‖∑ n ∈ kRange X R, f n‖ ≤ M)
    (hT : ∀ t : ℕ, ⌊X⌋₊ ≤ t → t ≤ ⌊X + R⌋₊ →
      ‖∑ n ∈ kRange (t : ℝ) (X + R - t), f n‖ ≤ M) :
    ∀ k, k ≤ ⌊X + R⌋₊ - ⌊X⌋₊ → ‖∑ i ∈ range k, f (⌊X⌋₊ + 1 + i)‖ ≤ 2 * M := by
  intro k hk
  have hfl : ⌊X⌋₊ ≤ ⌊X + R⌋₊ := Nat.floor_le_floor (by linarith)
  rw [initial_eq_full_sub_tail X R hX hR f k hk]
  refine (norm_sub_le _ _).trans ?_
  have := hT (⌊X⌋₊ + k) (by omega) (by omega)
  linarith

end LeanLab.Halupczok2012.Split398aMajorE2
