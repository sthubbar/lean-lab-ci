import LeanLab.ExceptionalSet.Feed1122p2_S133_lj1

/-!
Burst burst-20261122, session S133, wave 13. Split of `leaf_parity_detector_S133lj1` of
`Feed1122p2_S133_lj1.lean`, P0082 page 370 display 40, into Vaaler's sawtooth inequality.

Source of the leaf: J. D. Vaaler, Some extremal functions in Fourier analysis, Bull. Amer. Math.
Soc. 12 (1985), Theorem 18; also Graham and Kolesnik, Van der Corput's method of exponential sums,
Theorem A.6. For every `H ≥ 1` there is a trigonometric polynomial `V` of degree `H`, with
coefficients of size at most `1/(2π|m|)`, such that `|ψ(t) - V(t)|` is at most the Fejér kernel
`Δ_{H+1}(t)` divided by `2(H+1)`, where `ψ(t) = {t} - 1/2`.

The detector follows by the identity `1[[x] even] = 1/2 + ψ(x/2 - 1/2) - ψ(x/2)`, proved here: the
two Fejér kernels at `x/2` and `x/2 - 1/2` add up to a polynomial in the even frequencies of
`x/2`, that is in the integer frequencies of `x`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553c

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)

/-- LEAF: Vaaler 1985 Theorem 18, the sawtooth approximation used for the smoothing of P0082
page 370 display 40. Class MEDIUM, cited. For `H ≥ 1` there are coefficients `v m`, `|m| ≤ H`,
of norm at most `1`, such that for every real `t` the sawtooth `{t} - 1/2` differs from
`Σ_{|m| ≤ H} v m e(m t)` by at most `(1 + 2 Σ_{1 ≤ j ≤ H} (1 - j/(H+1)) cos(2π j t)) / (2(H+1))`. -/
theorem leaf_vaaler_sawtooth_S133lj1 : ∀ H : ℕ, 1 ≤ H →
    ∃ v : ℤ → ℂ, (∀ m, ‖v m‖ ≤ 1) ∧ ∀ t : ℝ,
      ‖(((Int.fract t - 1 / 2 : ℝ)) : ℂ) - ∑ m ∈ Finset.Icc (-(H : ℤ)) H, v m * eC ((m : ℝ) * t)‖ ≤
        1 / (2 * ((H : ℝ) + 1)) *
          (1 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
            Real.cos (2 * π * j * t)) := by
  sorry

namespace Feed1122p3S133lj1

/-- `1[[x] even] = 1/2 + {x/2 - 1/2} - {x/2}`. -/
theorem ind_eq (x : ℝ) :
    (if Even ⌊x⌋ then (1 : ℝ) else 0) = 1 / 2 + Int.fract (x / 2 - 1 / 2) - Int.fract (x / 2) := by
  have h0 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h1 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  rcases Int.even_or_odd ⌊x⌋ with ⟨q, hq⟩ | ⟨q, hq⟩
  · have hq' : (⌊x⌋ : ℝ) = 2 * q := by rw [hq]; push_cast; ring
    rw [if_pos ⟨q, hq⟩]
    have f1 : Int.fract (x / 2) = (x - ⌊x⌋) / 2 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, q, by rw [hq']; ring⟩
    have f2 : Int.fract (x / 2 - 1 / 2) = (x - ⌊x⌋ + 1) / 2 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, q - 1, by push_cast; rw [hq']; ring⟩
    rw [f1, f2]; ring
  · have hq' : (⌊x⌋ : ℝ) = 2 * q + 1 := by rw [hq]; push_cast; ring
    rw [if_neg (by rw [Int.not_even_iff_odd]; exact ⟨q, hq⟩)]
    have f1 : Int.fract (x / 2) = (x - ⌊x⌋ + 1) / 2 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, q, by rw [hq']; ring⟩
    have f2 : Int.fract (x / 2 - 1 / 2) = (x - ⌊x⌋) / 2 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, q, by rw [hq']; ring⟩
    rw [f1, f2]; ring

/-- The real part of `r e(θ)` for real `r`. -/
theorem re_ofReal_mul_eC (r θ : ℝ) : ((r : ℂ) * eC θ).re = r * Real.cos (2 * π * θ) := by
  simp only [eC]
  rw [show (2 * (π : ℂ) * Complex.I * (θ : ℂ)) = ((2 * π * θ : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The odd frequencies of the two Fejér kernels cancel. -/
theorem fejer_pair (H : ℕ) (y : ℝ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
        (Real.cos (2 * π * j * (y - 1 / 2)) + Real.cos (2 * π * j * y)) =
      ∑ k ∈ Finset.Icc (1 : ℕ) H, (if 2 * k ≤ H then
        2 * (1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1)) * Real.cos (2 * π * k * (2 * y)) else 0) := by
  set g : ℕ → ℝ := fun j => (1 - (j : ℝ) / ((H : ℝ) + 1)) *
        (Real.cos (2 * π * j * (y - 1 / 2)) + Real.cos (2 * π * j * y)) with hg
  have hcos : ∀ j : ℕ, Real.cos (2 * π * j * (y - 1 / 2)) = (-1) ^ j * Real.cos (2 * π * j * y) := by
    intro j
    have : 2 * π * j * (y - 1 / 2) = 2 * π * j * y - j * π := by ring
    rw [this, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]; ring
  have hodd : ∀ j ∈ Finset.Icc (1 : ℕ) H, g j ≠ 0 → Even j := by
    intro j _ hj
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    apply hj
    simp only [hg, hcos, hne.neg_one_pow]; ring
  rw [← Finset.sum_filter_of_ne hodd]
  have himg : (Finset.Icc (1 : ℕ) H).filter Even =
      ((Finset.Icc (1 : ℕ) H).filter (fun k => 2 * k ≤ H)).image (fun k => 2 * k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩
      exact ⟨k, ⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
      exact ⟨⟨by omega, h3⟩, ⟨k, by ring⟩⟩
  rw [himg, Finset.sum_image (fun a _ b _ hab => by omega), ← Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [hg, hcos, pow_mul, neg_one_sq, one_pow]
  have : 2 * π * ((2 * k : ℕ) : ℝ) * y = 2 * π * k * (2 * y) := by push_cast; ring
  rw [this]; ring


/-- `e(0) = 1`. -/
theorem eC_zero : eC 0 = 1 := by simp [eC]

end Feed1122p3S133lj1

/-- `leaf_parity_detector_S133lj1`, statement verbatim, from Vaaler's sawtooth leaf
`leaf_vaaler_sawtooth_S133lj1`, with `C = 3`: `P(x) = 1/2 + V(x/2 - 1/2) - V(x/2)`. -/
theorem leaf_parity_detector_S133lj1_split :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H →
      ∃ (a : ℤ → ℂ) (q₀ : ℝ) (b : ℕ → ℂ),
        (∀ h, ‖a h‖ ≤ C) ∧ 0 ≤ q₀ ∧ q₀ ≤ C / H ∧ (∀ k, ‖b k‖ ≤ C) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, a h * eC (-((h : ℝ) / 2) * x)‖ ≤
            q₀ + (∑ k ∈ Finset.Icc (1 : ℕ) H, b k * eC ((k : ℝ) * x)).re := by
  refine ⟨3, by norm_num, fun H hH => ?_⟩
  obtain ⟨v, hv, hV⟩ := leaf_vaaler_sawtooth_S133lj1 H hH
  have hH0 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH1 : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  refine ⟨fun h => (if h = 0 then (1 / 2 : ℂ) else 0) + v (-h) * (eC ((h : ℝ) / 2) - 1),
    1 / ((H : ℝ) + 1),
    fun k => if 2 * k ≤ H then
      (((2 / ((H : ℝ) + 1)) * (1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) else 0,
    ?_, by positivity, ?_, ?_, ?_⟩
  · intro h
    have e1 : ‖(if h = 0 then (1 / 2 : ℂ) else 0)‖ ≤ 1 / 2 := by
      split_ifs <;> norm_num
    have e2 : ‖eC ((h : ℝ) / 2) - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Feed1122p2S133lj1.norm_eC]; norm_num
    have e3 : ‖v (-h) * (eC ((h : ℝ) / 2) - 1)‖ ≤ 2 := by
      rw [norm_mul]
      calc ‖v (-h)‖ * ‖eC ((h : ℝ) / 2) - 1‖ ≤ 1 * 2 :=
            mul_le_mul (hv _) e2 (norm_nonneg _) zero_le_one
        _ = 2 := by ring
    exact (norm_add_le _ _).trans (by linarith)
  · rw [div_le_div_iff₀ hH1 (by linarith)]; nlinarith
  · intro k
    dsimp only
    split_ifs with hk
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have hk' : ((2 * k : ℕ) : ℝ) ≤ H := by exact_mod_cast hk
      have w0 : 0 ≤ 1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1) := by
        rw [sub_nonneg, div_le_one hH1]; linarith
      have w1 : 1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1) ≤ 1 := by
        have : 0 ≤ ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1) := by positivity
        linarith
      have t0 : 2 / ((H : ℝ) + 1) ≤ 1 := by rw [div_le_one hH1]; linarith
      rw [abs_of_nonneg (by positivity)]
      calc 2 / ((H : ℝ) + 1) * (1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1)) ≤ 1 * 1 :=
            mul_le_mul t0 w1 w0 zero_le_one
        _ ≤ 3 := by norm_num
    · simp
  · intro x
    set V : ℝ → ℂ := fun t => ∑ m ∈ Finset.Icc (-(H : ℤ)) H, v m * eC ((m : ℝ) * t) with hVdef
    set A : ℝ → ℝ := fun t => 1 / (2 * ((H : ℝ) + 1)) *
          (1 + 2 * ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
            Real.cos (2 * π * j * t)) with hAdef
    -- the approximant
    have hP : ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        ((if h = 0 then (1 / 2 : ℂ) else 0) + v (-h) * (eC ((h : ℝ) / 2) - 1)) *
          eC (-((h : ℝ) / 2) * x) = 1 / 2 + (V (x / 2 - 1 / 2) - V (x / 2)) := by
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_eq_single (0 : ℤ)]
        · simp [Feed1122p3S133lj1.eC_zero]
        · intro h _ hne; simp [hne]
        · intro h; exfalso; apply h; rw [Finset.mem_Icc]; constructor <;> omega
      · rw [hVdef]
        simp only
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_nbij' (fun h => -h) (fun h => -h) ?_ ?_ ?_ ?_ ?_
        · intro h hh; simp only [Finset.mem_coe, Finset.mem_Icc] at hh ⊢; omega
        · intro h hh; simp only [Finset.mem_coe, Finset.mem_Icc] at hh ⊢; omega
        · intro h _; simp
        · intro h _; simp
        · intro h _
          try simp only [neg_neg]
          rw [mul_assoc, sub_mul, one_mul, mul_sub, ← Feed1122p2S133lj1.eC_add]
          congr 2 <;> push_cast <;> ring
    -- the indicator
    have hind : (if Even ⌊x⌋ then (1 : ℂ) else 0) =
        ((1 / 2 + Int.fract (x / 2 - 1 / 2) - Int.fract (x / 2) : ℝ) : ℂ) := by
      rw [← Feed1122p3S133lj1.ind_eq]; split_ifs <;> simp
    have hdiff : (if Even ⌊x⌋ then (1 : ℂ) else 0) -
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
          ((if h = 0 then (1 / 2 : ℂ) else 0) + v (-h) * (eC ((h : ℝ) / 2) - 1)) *
            eC (-((h : ℝ) / 2) * x) =
        ((((Int.fract (x / 2 - 1 / 2) - 1 / 2 : ℝ)) : ℂ) - V (x / 2 - 1 / 2)) -
          ((((Int.fract (x / 2) - 1 / 2 : ℝ)) : ℂ) - V (x / 2)) := by
      rw [hP, hind]; push_cast; ring
    have hle : ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
          ((if h = 0 then (1 / 2 : ℂ) else 0) + v (-h) * (eC ((h : ℝ) / 2) - 1)) *
            eC (-((h : ℝ) / 2) * x)‖ ≤ A (x / 2 - 1 / 2) + A (x / 2) := by
      rw [hdiff]
      exact (norm_sub_le _ _).trans (add_le_add (hV _) (hV _))
    refine hle.trans (le_of_eq ?_)
    -- the majorant
    rw [Complex.re_sum]
    have hb : ∀ k ∈ Finset.Icc (1 : ℕ) H,
        ((if 2 * k ≤ H then
          (((2 / ((H : ℝ) + 1)) * (1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) else 0) *
            eC ((k : ℝ) * x)).re =
        1 / ((H : ℝ) + 1) * (if 2 * k ≤ H then
          2 * (1 - ((2 * k : ℕ) : ℝ) / ((H : ℝ) + 1)) * Real.cos (2 * π * k * (2 * (x / 2)))
          else 0) := by
      intro k _
      split_ifs
      · rw [Feed1122p3S133lj1.re_ofReal_mul_eC]
        have : 2 * π * ((k : ℝ) * x) = 2 * π * k * (2 * (x / 2)) := by ring
        rw [this]; field_simp
      · simp
    rw [Finset.sum_congr rfl hb, ← Finset.mul_sum, ← Feed1122p3S133lj1.fejer_pair]
    simp only [hAdef]
    have hsplit : ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
        (Real.cos (2 * π * j * (x / 2 - 1 / 2)) + Real.cos (2 * π * j * (x / 2))) =
        ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
          Real.cos (2 * π * j * (x / 2 - 1 / 2)) +
        ∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
          Real.cos (2 * π * j * (x / 2)) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit]
    generalize (∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
          Real.cos (2 * π * j * (x / 2 - 1 / 2))) = S1
    generalize (∑ j ∈ Finset.Icc (1 : ℕ) H, (1 - (j : ℝ) / ((H : ℝ) + 1)) *
          Real.cos (2 * π * j * (x / 2))) = S2
    field_simp
    ring

#print axioms Feed1122p3S133lj1.ind_eq
#print axioms Feed1122p3S133lj1.fejer_pair

/-- The split matches the parent statement exactly. -/
example : type_of% @leaf_parity_detector_S133lj1_split =
    type_of% @leaf_parity_detector_S133lj1 := rfl
end LeanLab.ExceptionalSet.Decomp553c
