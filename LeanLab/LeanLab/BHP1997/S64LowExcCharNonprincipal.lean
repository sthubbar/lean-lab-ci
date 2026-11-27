/-
Route burst burst-20261122, session S64, BHP1997, route step
`LowerShortC165.lower_exceptional_mean_square`, next open LEAF `Prep1121LowExc.leaf_char_nonprincipal`.

P0069 Baker Harman Pintz 1997, proof of Lemma 29 on pages 43 and 44, the case
`χ ∈ F = E_q^c \ {χ0}`. The paper's proof has two cited steps, which become two LEAFs here:
* `leaf_perron_window`: page 43 to 44, "by [29] Lemma 3.19" the window sum equals the Perron
  integral at height `Y` plus `O(Y^ε)`, pointwise in `y`; CITED Titchmarsh Lemma 3.19;
* `leaf_mellin_mean_value`: page 44, "By a variant of [8], Lemma 2", for any continuous
  `g`; CITED Gallagher [8] Lemma 2.
`leaf_perron_mean_square` is PROVED from `leaf_mellin_mean_value` and the proved kernel bound
`DQLeaf518Split.lemma29_ineq_six`: the mean square over `y` of the Perron integral is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, the first step of the display after 5.4.
`leaf_char_nonprincipal_of_leaves` is PROVED from the two leaves, with exactly the statement
of `Prep1121LowExc.leaf_char_nonprincipal`, checked by `leaf_char_nonprincipal_split_twin`.
The step that joins them, `|a|^2 ≤ 2|a-b|^2 + 2|b|^2` integrated over `[Y/2, 3Y]`, is the
tacit triangle step of page 44.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.Prep1121LowExcLemma29
import LeanLab.ExceptionalSet.WindowParseval264
import LeanLab.DERZ1997.Perron136

namespace LeanLab.BHP1997.S64LowExcCharNP
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory
open LeanLab.DERZ1997.Decomp1529b LeanLab.DERZ1997.Perron136

/-! ### The truncated Perron kernel at abscissa `1/2`, and the divisor bound

Private helpers for `leaf_perron_window`, P0069 page 43 to 44, [29] Titchmarsh Lemma 3.19.
The Perron kernel `perronI` and its three estimates are the proved lab port
`LeanLab.DERZ1997.Perron136` (Davenport chapter 17, page 105). -/

/-- Quotients of complex powers of positive reals. -/
private theorem cpow_div_cpow_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (s : ℂ) :
    (A : ℂ) ^ s / (B : ℂ) ^ s = ((A / B : ℝ) : ℂ) ^ s := by
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hAB : (0 : ℝ) < A / B := div_pos hA hB
  have h1 : Complex.log (A : ℂ) = (Real.log A : ℂ) := (Complex.ofReal_log hA.le).symm
  have h2 : Complex.log (B : ℂ) = (Real.log B : ℂ) := (Complex.ofReal_log hB.le).symm
  have h3 : Complex.log ((A / B : ℝ) : ℂ) = (Real.log (A / B) : ℂ) :=
    (Complex.ofReal_log hAB.le).symm
  have h4 : Real.log (A / B) = Real.log A - Real.log B := Real.log_div hA.ne' hB.ne'
  rw [Complex.cpow_def_of_ne_zero hAc, Complex.cpow_def_of_ne_zero hBc,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hAB.ne'), h1, h2, h3, h4]
  push_cast
  rw [← Complex.exp_sub]
  congr 1
  ring

/-- Multiplying a positive-base power by a nonzero integer power recovers the base power. -/
private theorem cpow_div_mul_nat {A : ℝ} (hA : 0 < A) {k : ℕ} (hk : k ≠ 0) (s : ℂ) :
    ((A / k : ℝ) : ℂ) ^ s * (k : ℂ) ^ s = (A : ℂ) ^ s := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkc : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; ring
  have hne : ((k : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hkc]
    exact Complex.exp_ne_zero _
  rw [← hcast, ← cpow_div_cpow_pos hA hkpos s]
  exact div_mul_cancel₀ _ hne

/-- The truncated Perron kernel at abscissa `1/2` on a positive base is continuous. -/
private theorem halfKernel_continuous {u : ℝ} (hu : 0 < u) :
    Continuous fun t : ℝ => (u : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
      ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  have hhalf : Continuous fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  refine Continuous.div (hhalf.const_cpow (Or.inl (by exact_mod_cast hu.ne'))) hhalf ?_
  intro t ht
  have h := congrArg Complex.re ht
  simp at h

/-- The difference of two kernels weighted by a nonzero integer power is continuous. -/
private theorem cpow_diff_continuous {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {k : ℕ} (hk : k ≠ 0) :
    Continuous fun t : ℝ =>
      (((A : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - ((B : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) /
        ((k : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) * ((1 / 2 : ℂ) + (t : ℂ) * I))) := by
  have hhalf : Continuous fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcA : Continuous fun t : ℝ => (A : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hhalf.const_cpow (Or.inl (by exact_mod_cast hA.ne'))
  have hcB : Continuous fun t : ℝ => ((B : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hhalf.const_cpow (Or.inl (by exact_mod_cast hB.ne'))
  have hck : Continuous fun t : ℝ => (k : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hhalf.const_cpow (Or.inl hkc)
  refine Continuous.div (hcA.sub hcB) (hck.mul hhalf) (fun t ht => ?_)
  have hkz : (k : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hkc]
    exact Complex.exp_ne_zero _
  have hs : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  exact mul_ne_zero hkz hs ht

/-- The difference of two kernels at abscissa `1/2` is continuous. -/
private theorem cpow_sub_half_continuous {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Continuous fun t : ℝ =>
      ((A : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) / ((1 / 2 : ℂ) + (t : ℂ) * I) -
        ((B : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) / ((1 / 2 : ℂ) + (t : ℂ) * I)) :=
  ((halfKernel_continuous hA).sub (halfKernel_continuous hB))

/-- The one-term truncated Perron integral against `w^(1/2+it)`, as `2π` times `perronI`. -/
private theorem integral_half_kernel {w T : ℝ} :
    (∫ t in (-T)..T, ((w : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
        ((1 / 2 : ℂ) + (t : ℂ) * I))
      = ((2 * Real.pi : ℝ) : ℂ) * perronI w (1 / 2) T := by
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast h.ne'
  have h2' : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := h2pi
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h
  have h1 : perronI w (1 / 2) T = (1 / (2 * Real.pi) : ℂ) *
      (∫ t in (-T)..T, ((w : ℝ) : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) /
        (((1 / 2 : ℝ) : ℂ) + t * I)) := rfl
  have h12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hscalar : (2 * (Real.pi : ℂ)) * (1 / (2 * (Real.pi : ℂ))) = 1 := by
    rw [mul_one_div, div_self h2']
  rw [h1, h12]
  push_cast
  rw [← mul_assoc, hscalar, one_mul]

/-- Linearity of the Perron integral over the finite Dirichlet polynomial: `1/2π` times the
integral of the polynomial times the difference of two cut kernels is the sum over `m` of the
coefficients times the difference of the per-term truncated Perron integrals. -/
private theorem perron_sum_identity (J : Finset ℕ) (hJ : ∀ m ∈ J, 1 ≤ m) (a : ℕ → ℂ)
    (T w1 w2 : ℝ) (hw1 : 0 < w1) (hw2 : 0 < w2) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T,
          (∑ m ∈ J, a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
            ((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
              (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ∑ m ∈ J, a m * (perronI (w1 / m) (1 / 2) T - perronI (w2 / m) (1 / 2) T) := by
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast h.ne'
  have hpt : ∀ t : ℝ,
      (∑ m ∈ J, a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
        ((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ∑ m ∈ J, a m * (((w1 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) -
        ((w2 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    intro t
    rw [Finset.sum_mul (s := J)
      (f := fun m : ℕ => a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))
      (a := ((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))), Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := hJ m hm
    have hm0 : m ≠ 0 := by omega
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hms : ((m : ℂ)) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0)]
      exact Complex.exp_ne_zero _
    have hs : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h
      have h1 := congrArg Complex.re h
      simp at h1
    have hP1 : (w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
        = ((w1 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [← cpow_div_mul_nat hw1 hm0 ((1 / 2 : ℂ) + (t : ℂ) * I),
        mul_div_cancel_right₀ _ hms]
    have hP2 : (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
        = ((w2 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
      rw [← cpow_div_mul_nat hw2 hm0 ((1 / 2 : ℂ) + (t : ℂ) * I),
        mul_div_cancel_right₀ _ hms]
    have hstep : a m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
        ((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)
        = a m * (((w1 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
            (w2 : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) := by
      field_simp
    rw [hstep, sub_div, hP1, hP2, mul_div_assoc, sub_div]
  have hint : ∀ m ∈ J, IntervalIntegrable
      (fun t : ℝ => a m * (((w1 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) -
        ((w2 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I))) MeasureTheory.volume (-T) T := by
    intro m hm
    have hm0 : m ≠ 0 := by have := hJ m hm; omega
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    exact (continuous_const.mul
      (cpow_sub_half_continuous (div_pos hw1 hmp) (div_pos hw2 hmp))).intervalIntegrable _ _
  have hper : ∀ m ∈ J,
      (∫ t in (-T)..T, a m * (((w1 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) -
        ((w2 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)))
      = a m * (((2 * Real.pi : ℝ) : ℂ) * perronI (w1 / m) (1 / 2) T -
          ((2 * Real.pi : ℝ) : ℂ) * perronI (w2 / m) (1 / 2) T) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := hJ m hm; omega
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hi1 : IntervalIntegrable
        (fun t : ℝ => ((w1 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) MeasureTheory.volume (-T) T :=
      (halfKernel_continuous (div_pos hw1 hmp)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun t : ℝ => ((w2 / m : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) MeasureTheory.volume (-T) T :=
      (halfKernel_continuous (div_pos hw2 hmp)).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
      integral_half_kernel (w := w1 / m) (T := T),
      integral_half_kernel (w := w2 / m) (T := T)]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_finsetSum hint,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hper m hm]
  have hc2 : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ) = 1 :=
    inv_mul_cancel₀ h2pi
  calc ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (a m *
        (((2 * Real.pi : ℝ) : ℂ) * perronI (w1 / m) (1 / 2) T -
          ((2 * Real.pi : ℝ) : ℂ) * perronI (w2 / m) (1 / 2) T))
      = a m * ((((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ)) *
            perronI (w1 / m) (1 / 2) T -
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((2 * Real.pi : ℝ) : ℂ)) *
            perronI (w2 / m) (1 / 2) T) := by ring
    _ = a m * (perronI (w1 / m) (1 / 2) T - perronI (w2 / m) (1 / 2) T) := by
        rw [hc2]; ring

/-- Davenport chapter 17, page 105, as in [29] Titchmarsh Lemma 3.19: the truncated Perron
integral `perronI w c T = (1/2π) ∫_{-T}^{T} w^(c+it)/(c+it) dt` differs from the step
`H = [w > 1]`, with any value at `w = 1`, by at most `2 w^c / (1 + T |log w|)`. -/
private theorem perron_term_bound {w c T : ℝ} (hw : 0 < w) (hc : 0 < c) (hT : 0 < T)
    (H : Prop) [Decidable H] (hH1 : 1 < w → H) (hH2 : w < 1 → ¬H) :
    ‖(if H then (1 : ℂ) else 0) - perronI w c T‖ ≤ 2 * (w ^ c / (1 + T * |Real.log w|)) := by
  have hwc : 0 < w ^ c := Real.rpow_pos_of_pos hw c
  have hd : 0 < 1 + T * |Real.log w| :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hT.le (abs_nonneg _))
  rcases lt_trichotomy w 1 with h | h | h
  · rw [if_neg (hH2 h), zero_sub, norm_neg]
    by_cases ha : T * |Real.log w| ≤ 1
    · calc ‖perronI w c T‖ ≤ w ^ c := perron_norm_small hw hc hT ha
        _ ≤ _ := by
          rw [mul_div_assoc', le_div_iff₀ hd]; nlinarith
    · push_neg at ha
      have hrem := perron_remainder_bound (c := c) (T := T) hw h.ne hc hT
      simp only [not_lt_of_gt h, if_false, sub_zero] at hrem
      have hp : 1 + T * |Real.log w| ≤ 2 * (Real.pi * T * |Real.log w|) := by
        nlinarith [Real.pi_gt_three]
      calc ‖perronI w c T‖ ≤ _ := hrem
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT)
            (abs_pos.2 (Real.log_ne_zero_of_pos_of_ne_one hw h.ne))) hd]
          nlinarith [mul_le_mul_of_nonneg_left hp hwc.le]
  · subst h
    have hP : ‖perronI 1 c T‖ ≤ 1 := by
      have := perron_norm_small (y := 1) (c := c) (T := T) one_pos hc hT (by simp)
      simpa using this
    have hH : ‖(if H then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc _ ≤ ‖(if H then (1 : ℂ) else 0)‖ + ‖perronI 1 c T‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
      _ = _ := by simp
  · rw [if_pos (hH1 h), norm_sub_rev]
    have hl : 0 < Real.log w := Real.log_pos h
    rw [abs_of_pos hl] at hd ⊢
    by_cases ha : T * Real.log w ≤ 1
    · calc ‖perronI w c T - 1‖ ≤ w ^ c := perron_gt_one_small h hc hT ha
        _ ≤ _ := by
          rw [mul_div_assoc', le_div_iff₀ hd]; nlinarith
    · push_neg at ha
      have hrem := perron_remainder_bound (c := c) (T := T) hw h.ne' hc hT
      simp only [h, if_true, abs_of_pos hl] at hrem
      have hp : 1 + T * Real.log w ≤ 2 * (Real.pi * T * Real.log w) := by
        nlinarith [Real.pi_gt_three]
      calc ‖perronI w c T - 1‖ ≤ _ := hrem
        _ ≤ _ := by
          rw [mul_div_assoc', div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) hl) hd]
          nlinarith [mul_le_mul_of_nonneg_left hp hwc.le]

/-- Every `m` in the polynomial support is a positive integer. -/
private theorem rightInterval_one_le {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) : 1 ≤ m := by
  unfold rightInterval at hm
  rw [Finset.mem_Ioc] at hm
  omega

/-- Page 5 coefficient input: the divisor count is bounded by every positive power. -/
private theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let B : ℝ := 1 + 1 / (r - 1)
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [one_div_pos.mpr (sub_pos.mpr hr)]
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨K, hK⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  have hlarge {p : ℕ} (hp : K ≤ p) : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc
      _ = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
        (hK.trans (Nat.cast_le.mpr hp)) hε.le
  have hsmall (k : ℕ) : (k : ℝ) + 1 ≤ B * r ^ k := by
    have hk := k.cast_le_pow_div_sub hr
    have hpow : 1 ≤ r ^ k := one_le_pow₀ hr.le
    calc
      _ ≤ r ^ k / (r - 1) + r ^ k := add_le_add hk hpow
      _ = _ := by dsimp [B]; ring
  let c : ℕ → ℝ := fun p => if p < K then B else 1
  have hc (p : ℕ) : 1 ≤ c p := by dsimp [c]; split_ifs <;> linarith
  have hfactor (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ c p * ((p : ℝ) ^ k) ^ ε := by
    have hpe : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num)
      (by exact_mod_cast hp.two_le) hε.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg p)]
    by_cases hpK : p < K
    · dsimp [c]
      rw [if_pos hpK]
      exact (hsmall k).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpe k) hB0.le)
    · dsimp [c]
      rw [if_neg hpK, one_mul]
      have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
        exact_mod_cast (Nat.lt_two_pow_self (n := k)).succ_le
      exact hk.trans (pow_le_pow_left₀ (by norm_num) (hlarge (by omega)) k)
  refine ⟨B ^ K, pow_pos hB0 K, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (ne_of_gt hε)]
  have hprod : (∏ p ∈ n.primeFactors, c p) ≤ B ^ K := by
    calc
      _ = ∏ p ∈ n.primeFactors.filter (fun p => p < K), B := by
        simp [c, Finset.prod_ite]
      _ = B ^ (n.primeFactors.filter (fun p => p < K)).card := by simp
      _ ≤ B ^ K := pow_le_pow_right₀ hB (by
        have hh := Finset.card_le_card (show n.primeFactors.filter (fun p => p < K) ⊆
            Finset.range K from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        simpa using hh)
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p hp => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      exact_mod_cast (Nat.card_divisors hn)
    _ ≤ ∏ p ∈ n.primeFactors, c p * ((p : ℝ) ^ n.factorization p) ^ ε :=
      Finset.prod_le_prod₀ (fun p hp => by positivity)
        (fun p hp => hfactor p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, c p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hpower]
    _ ≤ B ^ K * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hprod (by positivity)

/-- Page 3, display 3.1 with the divisor bound: on the polynomial support `(Y, 2Y]` every
coefficient is `≪ Y^(1/200)`, as used on page 44 for the error `O(Y^ε)`. -/
private theorem coeff_divisor (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      |b x m| ≤ K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
  obtain ⟨C₀, hC₀⟩ := hb
  have hx : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hdpos : ∀ m : ℕ, 1 ≤ m → (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by
    intro m hm
    have h1 : 0 < m.divisors.card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
    have h2 : 1 ≤ m.divisors.card := h1
    exact_mod_cast h2
  rcases le_or_gt B 0 with hB | hB
  · -- nonpositive divisor exponent: the coefficient is bounded outright
    refine ⟨max C₀ 0, le_max_right _ _, 1, ?_⟩
    intro x hx1 m hm
    have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 hx.le
    have hYp : (1 : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) :=
      Real.one_le_rpow hY1 (by norm_num)
    have hd1 : (1 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := hdpos m (rightInterval_one_le hm)
    have hdB : ((m.divisors.card : ℕ) : ℝ) ^ B ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hd1 hB
    calc |b x m| ≤ C₀ * ((m.divisors.card : ℕ) : ℝ) ^ B := hC₀ x m
      _ ≤ max C₀ 0 * 1 := by
          exact mul_le_mul (le_max_left _ _) hdB (by positivity) (le_max_right _ _)
      _ ≤ max C₀ 0 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
          calc max C₀ 0 * 1 = max C₀ 0 := mul_one _
            _ ≤ max C₀ 0 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) :=
                le_mul_of_one_le_right (le_max_right _ _) hYp
  · -- positive divisor exponent: `d(m)^B ≤ C m^(1/400) ≤ C (2Y)^(1/400)`
    obtain ⟨Cd, hCd, hCdle⟩ := card_divisors_le_rpow (ε := 1 / (400 * B)) (by positivity)
    refine ⟨max C₀ 0 * Cd ^ B * 2, by positivity, 1, ?_⟩
    intro x hx1 m hm
    have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 hx.le
    have hY0 : (0 : ℝ) < x ^ (11 / 20 + ε) := by linarith
    have hm1 : 1 ≤ m := rightInterval_one_le hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hm2 : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
      unfold rightInterval at hm
      rw [Finset.mem_Ioc] at hm
      have h1 : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hm.2
      have h2 : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
        Nat.floor_le (by positivity)
      linarith
    have hdm : ((m.divisors.card : ℕ) : ℝ) ≤ Cd * (m : ℝ) ^ (1 / (400 * B)) := hCdle m
    have hpow : ((m.divisors.card : ℕ) : ℝ) ^ B ≤ Cd ^ B * (m : ℝ) ^ (1 / 400 : ℝ) := by
      calc ((m.divisors.card : ℕ) : ℝ) ^ B
          ≤ (Cd * (m : ℝ) ^ (1 / (400 * B))) ^ B :=
            Real.rpow_le_rpow (lt_of_lt_of_le zero_lt_one (hdpos m hm1)).le hdm hB.le
        _ = Cd ^ B * ((m : ℝ) ^ (1 / (400 * B))) ^ B :=
            Real.mul_rpow hCd.le (Real.rpow_nonneg hmpos.le _)
        _ = Cd ^ B * (m : ℝ) ^ (1 / (400 * B) * B) := by
            rw [Real.rpow_mul hmpos.le]
        _ = Cd ^ B * (m : ℝ) ^ (1 / 400 : ℝ) := by
            have hc : (1 : ℝ) / (400 * B) * B = 1 / 400 := by field_simp
            rw [hc]
    have h400 : (m : ℝ) ^ (1 / 400 : ℝ) ≤ 2 * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) := by
      have hstep : (m : ℝ) ^ (1 / 400 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) :=
        Real.rpow_le_rpow hmpos.le hm2 (by norm_num)
      have hsplit : (2 * x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) =
          (2 : ℝ) ^ (1 / 400 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) :=
        Real.mul_rpow (by norm_num) hY0.le
      have htwo : (2 : ℝ) ^ (1 / 400 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 400 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      calc (m : ℝ) ^ (1 / 400 : ℝ) ≤ (2 : ℝ) ^ (1 / 400 : ℝ) *
              (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) := by rw [← hsplit]; exact hstep
        _ ≤ 2 * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) :=
            mul_le_mul_of_nonneg_right htwo (by positivity)
    have hYs : (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
    have hYp : (0 : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by positivity
    calc |b x m| ≤ C₀ * ((m.divisors.card : ℕ) : ℝ) ^ B := hC₀ x m
      _ ≤ max C₀ 0 * ((m.divisors.card : ℕ) : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C₀ 0 * (Cd ^ B * (m : ℝ) ^ (1 / 400 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      _ ≤ max C₀ 0 * (Cd ^ B * (2 * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ))) := by
          have hCd0 : (0 : ℝ) < Cd ^ B := Real.rpow_pos_of_pos hCd _
          have h1 : Cd ^ B * (m : ℝ) ^ (1 / 400 : ℝ) ≤
              Cd ^ B * (2 * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ)) :=
            mul_le_mul_of_nonneg_left h400 hCd0.le
          exact mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
      _ ≤ max C₀ 0 * Cd ^ B * 2 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
          have hCd0 : (0 : ℝ) ≤ Cd ^ B := (Real.rpow_pos_of_pos hCd _).le
          have h1 : Cd ^ B * (x ^ (11 / 20 + ε)) ^ (1 / 400 : ℝ) ≤
              Cd ^ B * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) :=
            mul_le_mul_of_nonneg_left hYs hCd0
          nlinarith [le_max_right C₀ 0, hYp, h1, hCd0]

/-- A sum of inverse distances to a fixed integer is at most twice the harmonic sum. -/
private theorem sum_inv_abs_sub_le (N m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤ 2 * (harmonic N : ℝ) := by
  have hleft : ∑ k ∈ Finset.Icc 1 (m - 1), (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤ (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun k : ℕ => m - k) ↑(Finset.Icc 1 (m - 1)) := by
      intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have h1 : a ≤ m := by omega
      have h2 : b ≤ m := by omega
      have hab' : m - a = m - b := hab
      calc a = m - (m - a) := (Nat.sub_sub_self h1).symm
        _ = m - (m - b) := by rw [hab']
        _ = b := Nat.sub_sub_self h2
    have hmap : Finset.image (fun k : ℕ => m - k) (Finset.Icc 1 (m - 1)) ⊆
        Finset.Icc 1 N := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hmain := Finset.sum_le_sum_of_injOn
      (f := fun k : ℕ => (|(k : ℝ) - (m : ℝ)|)⁻¹)
      (g := fun j : ℕ => ((j : ℝ))⁻¹) (fun k : ℕ => m - k) hinj hmap ?_ ?_
    · calc ∑ k ∈ Finset.Icc 1 (m - 1), (|(k : ℝ) - (m : ℝ)|)⁻¹
          ≤ ∑ j ∈ Finset.Icc 1 N, ((j : ℝ))⁻¹ := hmain
        _ = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hkm : k ≤ m := by omega
      have hkr : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
      have habs : |(k : ℝ) - (m : ℝ)| = ((m - k : ℕ) : ℝ) := by
        rw [abs_of_nonpos (by linarith : (k : ℝ) - (m : ℝ) ≤ 0), Nat.cast_sub hkm]
        ring
      rw [habs]
    · intro a ha hna
      positivity
  have hright : ∑ k ∈ Finset.Icc (m + 1) N, (|(k : ℝ) - (m : ℝ)|)⁻¹ ≤
      (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun k : ℕ => k - m) ↑(Finset.Icc (m + 1) N) := by
      intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have h1 : m ≤ a := by omega
      have h2 : m ≤ b := by omega
      have hab' : a - m = b - m := hab
      calc a = (a - m) + m := (Nat.sub_add_cancel h1).symm
        _ = (b - m) + m := by rw [hab']
        _ = b := Nat.sub_add_cancel h2
    have hmap : Finset.image (fun k : ℕ => k - m) (Finset.Icc (m + 1) N) ⊆
        Finset.Icc 1 N := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    have hmain := Finset.sum_le_sum_of_injOn
      (f := fun k : ℕ => (|(k : ℝ) - (m : ℝ)|)⁻¹)
      (g := fun j : ℕ => ((j : ℝ))⁻¹) (fun k : ℕ => k - m) hinj hmap ?_ ?_
    · calc ∑ k ∈ Finset.Icc (m + 1) N, (|(k : ℝ) - (m : ℝ)|)⁻¹
          ≤ ∑ j ∈ Finset.Icc 1 N, ((j : ℝ))⁻¹ := hmain
        _ = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]
            simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have hmk : m ≤ k := by omega
      have hkr : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
      have habs : |(k : ℝ) - (m : ℝ)| = ((k - m : ℕ) : ℝ) := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ)), Nat.cast_sub hmk]
      rw [habs]
    · intro a ha hna
      positivity
  have hsub : Finset.Icc 1 N ⊆ (Finset.Icc 1 (m - 1) ∪ {m}) ∪ Finset.Icc (m + 1) N := by
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton] at hk ⊢
    rcases lt_trichotomy k m with h | h | h
    · exact Or.inl (Or.inl ⟨hk.1, by omega⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨by omega, hk.2⟩
  have hnn : ∀ k ∈ (Finset.Icc 1 (m - 1) ∪ {m}) ∪ Finset.Icc (m + 1) N,
      k ∉ Finset.Icc 1 N → 0 ≤ (|(k : ℝ) - (m : ℝ)|)⁻¹ := by
    intro k _ _
    positivity
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hd1 : Disjoint (Finset.Icc 1 (m - 1) ∪ {m}) (Finset.Icc (m + 1) N) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at ha hb
    omega
  have hd2 : Disjoint (Finset.Icc 1 (m - 1)) ({m} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc, Finset.mem_singleton] at ha hb
    omega
  rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton] at hmono
  have hfm : (|((m : ℕ) : ℝ) - (m : ℝ)|)⁻¹ = 0 := by simp
  rw [hfm, add_zero] at hmono
  linarith

/-- `|log r| ≥ |r - 1| / 12` on `[1/4, 6]`. -/
private theorem abs_log_ge {r : ℝ} (hr1 : 1 / 4 ≤ r) (hr2 : r ≤ 6) :
    |r - 1| / 12 ≤ |Real.log r| := by
  have hr0 : (0 : ℝ) < r := by linarith
  rcases le_or_gt 1 r with h | h
  · have hlog : (r - 1) / r ≤ Real.log r := by
      have hx := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / r by positivity)
      have h2 : Real.log (1 / r) = -Real.log r := by
        rw [Real.log_div one_ne_zero hr0.ne', Real.log_one]; ring
      have h3 : (1 : ℝ) / r - 1 = -(r - 1) / r := by field_simp; ring
      rw [h2, h3] at hx
      have h5 : -((1 - r) / r) ≤ Real.log r := by simpa using neg_le_neg hx
      rw [show -((1 - r) / r) = (r - 1) / r by ring] at h5
      exact h5
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r - 1),
      abs_of_nonneg (Real.log_nonneg h)]
    calc (r - 1) / 12 ≤ (r - 1) / r := by
          apply div_le_div_of_nonneg_left (by linarith) hr0 (by linarith)
      _ ≤ Real.log r := hlog
  · have hlt : r ≤ 1 := h.le
    have hlog : 1 - r ≤ -Real.log r := by
      have hx := Real.log_le_sub_one_of_pos hr0
      linarith
    rw [abs_of_nonpos (by linarith : r - 1 ≤ 0),
      abs_of_nonpos (Real.log_nonpos hr0.le hlt)]
    linarith

/-- Sum of `1/(1+|w-m|)` over `[1,N]` is at most `4 H_N + 3`. -/
private theorem sum_inv_one_add_dist_le (w : ℝ) (N : ℕ) (hw1 : 1 ≤ w) :
    ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹ ≤ 4 * (harmonic N : ℝ) + 3 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  set M : ℕ := min N ⌊w⌋₊ with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact le_min hN ((Nat.one_le_floor_iff w).mpr hw1)
  have hMN : M ≤ N := by rw [hMdef]; exact min_le_left _ _
  have hCases : (M = ⌊w⌋₊ ∧ ⌊w⌋₊ ≤ N) ∨ (M = N ∧ N ≤ ⌊w⌋₊) := by
    rw [hMdef]
    rcases le_total ⌊w⌋₊ N with h | h
    · exact Or.inl ⟨min_eq_right h, h⟩
    · exact Or.inr ⟨min_eq_left h, h⟩
  have hw0 : (0 : ℝ) < w := by linarith
  have hkey : ∀ m ∈ Finset.Icc 1 N,
      (1 + |w - (m : ℝ)|)⁻¹ ≤ 2 * (|(M : ℝ) - (m : ℝ)|)⁻¹ +
        (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hdist : |(M : ℝ) - (m : ℝ)| ≤ 1 + |w - (m : ℝ)| := by
      rcases hCases with ⟨hc, hNle⟩ | ⟨hc, hNle⟩
      · have hf : |(M : ℝ) - w| ≤ 1 := by
          rw [hc]
          simpa using Nat.abs_floor_sub_le (a := w) hw0.le
        calc |(M : ℝ) - (m : ℝ)| = |((M : ℝ) - w) + (w - (m : ℝ))| := by ring_nf
          _ ≤ |(M : ℝ) - w| + |w - (m : ℝ)| := abs_add_le _ _
          _ ≤ 1 + |w - (m : ℝ)| := by linarith
      · have hmM : m ≤ M := by rw [hc]; exact hm.2
        have hMw : (M : ℝ) ≤ w := by
          rw [hc]
          exact (Nat.cast_le.mpr hNle).trans (Nat.floor_le hw0.le)
        have hmw : (m : ℝ) ≤ w := (Nat.cast_le.mpr hmM).trans hMw
        have hMm : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
        have hdiff : |(M : ℝ) - (m : ℝ)| = (M : ℝ) - (m : ℝ) := by
          rw [abs_of_nonneg]; linarith
        have hwdiff : |w - (m : ℝ)| = w - (m : ℝ) := by
          rw [abs_of_nonneg]; linarith
        rw [hdiff, hwdiff]; linarith
    have hd0 : (0 : ℝ) < 1 + |w - (m : ℝ)| := by positivity
    rcases le_or_gt (|(M : ℝ) - (m : ℝ)|) 1 with hle1 | hgt1
    · have hind : (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0) = 1 := if_pos hle1
      rw [hind]
      have h1 : (1 + |w - (m : ℝ)|)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hd0]
        linarith [abs_nonneg (w - (m : ℝ))]
      have h2 : (0 : ℝ) ≤ 2 * (|(M : ℝ) - (m : ℝ)|)⁻¹ := by positivity
      linarith
    · have hind : (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0) = 0 :=
        if_neg (not_le.mpr hgt1)
      rw [hind, add_zero]
      have hhalf : |(M : ℝ) - (m : ℝ)| / 2 ≤ 1 + |w - (m : ℝ)| := by linarith
      have hpos : (0 : ℝ) < |(M : ℝ) - (m : ℝ)| / 2 := by linarith
      calc (1 + |w - (m : ℝ)|)⁻¹ ≤ (|(M : ℝ) - (m : ℝ)| / 2)⁻¹ :=
            inv_anti₀ hpos hhalf
        _ = 2 * (|(M : ℝ) - (m : ℝ)|)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hstep : ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹
      ≤ 2 * (∑ m ∈ Finset.Icc 1 N, (|(M : ℝ) - (m : ℝ)|)⁻¹) +
        ∑ m ∈ Finset.Icc 1 N, (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hkey
  have hA : ∑ m ∈ Finset.Icc 1 N, (|(M : ℝ) - (m : ℝ)|)⁻¹ ≤ 2 * (harmonic N : ℝ) := by
    simpa only [abs_sub_comm] using sum_inv_abs_sub_le N M hM1 hMN
  have hcard : ((Finset.Icc 1 N).filter
      (fun m : ℕ => |(M : ℝ) - (m : ℝ)| ≤ 1)).card ≤ 3 := by
    have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => |(M : ℝ) - (m : ℝ)| ≤ 1) ⊆
        (Finset.Icc (M - 1) (M + 1) : Finset ℕ) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨h1, h2⟩, h3⟩ := hm
      rw [Finset.mem_Icc]
      constructor
      · have h4 : (M : ℝ) - (m : ℝ) ≤ 1 := (abs_le.mp h3).2
        have h5 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have h6 : (M : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by rw [h5]; linarith
        have h7 : M ≤ m + 1 := Nat.cast_le.mp h6
        omega
      · have h4 : -1 ≤ (M : ℝ) - (m : ℝ) := (abs_le.mp h3).1
        have h5 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        have h6 : (m : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by rw [h5]; linarith
        exact Nat.cast_le.mp h6
    calc ((Finset.Icc 1 N).filter (fun m : ℕ => |(M : ℝ) - (m : ℝ)| ≤ 1)).card
        ≤ (Finset.Icc (M - 1) (M + 1) : Finset ℕ).card := Finset.card_le_card hsub
      _ = 3 := by rw [Nat.card_Icc]; omega
  have hB : ∑ m ∈ Finset.Icc 1 N, (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0) ≤ 3 := by
    have hEq : ∑ m ∈ Finset.Icc 1 N,
        (if |(M : ℝ) - (m : ℝ)| ≤ 1 then (1 : ℝ) else 0)
        = (((Finset.Icc 1 N).filter
          (fun m : ℕ => |(M : ℝ) - (m : ℝ)| ≤ 1)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hEq]
    exact_mod_cast hcard
  linarith

/-- Page 44, the summed Perron remainder: for `w ≍ Y` the weighted sum of the cut errors is
`≪ log Y ≪ Y^(1/200)`. -/
private theorem log_sum_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ w : ℝ,
      x ^ (11 / 20 + ε) / 2 ≤ w → w ≤ 6 * x ^ (11 / 20 + ε) →
        ∑ m ∈ rightInterval ε x, (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
            (1 + x ^ (11 / 20 + ε) * |Real.log (w / (m : ℝ))|) ≤
          K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
  have ha : (0 : ℝ) < 11 / 20 + ε := by linarith
  refine ⟨1000000, by norm_num, (6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹), fun x hx w hw1 hw2 => ?_⟩
  set Y : ℝ := x ^ (11 / 20 + ε) with hY
  have hp6 : (0 : ℝ) < (6 : ℝ) ^ 16 := by positivity
  have hbig : (6 : ℝ) ^ 16 ≤ Y := by
    have hCn : (0 : ℝ) ≤ ((6 : ℝ) ^ 16) ^ (((11 / 20 + ε))⁻¹) := by positivity
    have h := Real.rpow_le_rpow hCn hx ha.le
    have h2 : (((6 : ℝ) ^ 16) ^ (((11 / 20 + ε))⁻¹)) ^ (11 / 20 + ε) = (6 : ℝ) ^ 16 :=
      Real.rpow_inv_rpow (x := (6 : ℝ) ^ 16) (y := 11 / 20 + ε) hp6.le ha.ne'
    rw [hY, ← h2]
    exact h
  have hY0 : (0 : ℝ) < Y := by
    linarith [show (0 : ℝ) < (6 : ℝ) ^ 16 from by positivity]
  have hY1 : (1 : ℝ) ≤ Y := by linarith [show (1 : ℝ) ≤ (6 : ℝ) ^ 16 from by norm_num]
  have hY4 : (4 : ℝ) ≤ Y := by linarith [show (4 : ℝ) ≤ (6 : ℝ) ^ 16 from by norm_num]
  set N : ℕ := ⌊2 * Y⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    apply (Nat.one_le_floor_iff (2 * Y)).mpr (by linarith)
  have hJsub : rightInterval ε x ⊆ Finset.Icc 1 N := by
    intro m hm
    unfold rightInterval at hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Icc]
    refine ⟨by omega, ?_⟩
    rw [hN]
    exact hm.2
  have hYp : (0 : ℝ) ≤ Y ^ (1 / 200 : ℝ) := by positivity
  have hpt : ∀ m ∈ rightInterval ε x,
      (w / (m : ℝ)) ^ (1 / 2 : ℝ) / (1 + Y * |Real.log (w / (m : ℝ))|) ≤
        96 * (1 + |w - (m : ℝ)|)⁻¹ := by
    intro m hm
    have hm1 : 1 ≤ m := rightInterval_one_le hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmY : Y < (m : ℝ) := by
      unfold rightInterval at hm
      rw [Finset.mem_Ioc] at hm
      have h1 : (⌊Y⌋₊ : ℝ) + 1 ≤ (m : ℝ) := by
        have h2 : ⌊Y⌋₊ + 1 ≤ m := hm.1
        exact_mod_cast h2
      have h3 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
      linarith
    have hm2Y : (m : ℝ) ≤ 2 * Y := by
      unfold rightInterval at hm
      rw [Finset.mem_Ioc] at hm
      have h1 : (m : ℝ) ≤ (⌊2 * Y⌋₊ : ℝ) := by exact_mod_cast hm.2
      have h2 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
      linarith
    have hr0 : (0 : ℝ) < w / (m : ℝ) := div_pos (by linarith) hmpos
    have hr1 : (1 : ℝ) / 4 ≤ w / (m : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hmpos]
      nlinarith
    have hr2 : w / (m : ℝ) ≤ 6 := by
      rw [div_le_iff₀ hmpos]
      nlinarith
    have hsqrt : (w / (m : ℝ)) ^ (1 / 2 : ℝ) ≤ 4 := by
      have h16 : w / (m : ℝ) ≤ 16 := by linarith
      have h := Real.rpow_le_rpow hr0.le h16 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have h4 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
        have h16 : (16 : ℝ) = 4 ^ (2 : ℝ) := by
          rw [Real.rpow_two]; norm_num
        rw [h16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      rwa [h4] at h
    have hlog := abs_log_ge hr1 hr2
    have hratio : |w / (m : ℝ) - 1| = |w - (m : ℝ)| / (m : ℝ) := by
      rw [show w / (m : ℝ) - 1 = (w - (m : ℝ)) / (m : ℝ) by field_simp]
      rw [abs_div, abs_of_pos hmpos]
    have hYlog : |w - (m : ℝ)| / 24 ≤ Y * |Real.log (w / (m : ℝ))| := by
      have h1 : Y * (|w - (m : ℝ)| / (12 * (m : ℝ))) ≤ Y * |Real.log (w / (m : ℝ))| := by
        have h2 : |w - (m : ℝ)| / (12 * (m : ℝ)) = |w / (m : ℝ) - 1| / 12 := by
          rw [hratio]; field_simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left hlog hY0.le
      have hcoef : (1 : ℝ) / 24 ≤ Y / (12 * (m : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith [hm2Y, hY0]
      have h3 : |w - (m : ℝ)| / 24 ≤ Y * (|w - (m : ℝ)| / (12 * (m : ℝ))) := by
        calc |w - (m : ℝ)| / 24 = |w - (m : ℝ)| * (1 / 24) := by ring
          _ ≤ |w - (m : ℝ)| * (Y / (12 * (m : ℝ))) :=
              mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
          _ = Y * (|w - (m : ℝ)| / (12 * (m : ℝ))) := by ring
      exact h3.trans h1
    have hden : (0 : ℝ) < 1 + Y * |Real.log (w / (m : ℝ))| := by positivity
    have hden2 : (0 : ℝ) < 1 + |w - (m : ℝ)| / 24 := by positivity
    have hstep : (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
        (1 + Y * |Real.log (w / (m : ℝ))|) ≤ 4 / (1 + |w - (m : ℝ)| / 24) := by
      have hA : (w / (m : ℝ)) ^ (1 / 2 : ℝ) / (1 + Y * |Real.log (w / (m : ℝ))|) ≤
          4 / (1 + Y * |Real.log (w / (m : ℝ))|) :=
        div_le_div_of_nonneg_right hsqrt hden.le
      have hB : 4 / (1 + Y * |Real.log (w / (m : ℝ))|) ≤ 4 / (1 + |w - (m : ℝ)| / 24) :=
        div_le_div_of_nonneg_left (by norm_num) hden2 (by linarith)
      linarith
    have hfin : 4 / (1 + |w - (m : ℝ)| / 24) = 96 / (24 + |w - (m : ℝ)|) := by
      field_simp
      ring
    have hfin2 : 96 / (24 + |w - (m : ℝ)|) ≤ 96 * (1 + |w - (m : ℝ)|)⁻¹ := by
      rw [mul_comm, ← div_eq_inv_mul]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [abs_nonneg (w - (m : ℝ))])
    rw [hfin] at hstep
    linarith
  have hstep1 : ∑ m ∈ rightInterval ε x, (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
        (1 + Y * |Real.log (w / (m : ℝ))|) ≤
      96 * ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹ := by
    calc ∑ m ∈ rightInterval ε x, (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
          (1 + Y * |Real.log (w / (m : ℝ))|)
        ≤ ∑ m ∈ rightInterval ε x, 96 * (1 + |w - (m : ℝ)|)⁻¹ := Finset.sum_le_sum hpt
      _ = 96 * ∑ m ∈ rightInterval ε x, (1 + |w - (m : ℝ)|)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 96 * ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hJsub (fun m _ _ => by positivity)
  have hH : ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹ ≤ 4 * (harmonic N : ℝ) + 3 :=
    sum_inv_one_add_dist_le w N (by linarith)
  have hlogN : (harmonic N : ℝ) ≤ 1 + 2 * Real.log Y := by
    have h1 : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have hNr : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := hN1
      exact_mod_cast this
    have hNle : (N : ℝ) ≤ 2 * Y := by
      rw [hN]
      exact Nat.floor_le (by linarith)
    have h2 : Real.log N ≤ Real.log (2 * Y) := Real.log_le_log hNr hNle
    have h3 : Real.log (2 * Y) ≤ 2 * Real.log Y := by
      have h4 : 2 * Y ≤ Y * Y := by nlinarith
      calc Real.log (2 * Y) ≤ Real.log (Y * Y) := Real.log_le_log (by linarith) h4
        _ = 2 * Real.log Y := by rw [Real.log_mul hY0.ne' hY0.ne']; ring
    linarith
  have hlogY : Real.log Y ≤ 400 * Y ^ (1 / 400 : ℝ) := by
    have h := Real.log_le_rpow_div hY0.le (show (0 : ℝ) < 1 / 400 by norm_num)
    have h2 : (1 : ℝ) / 400 = 400⁻¹ := by norm_num
    calc Real.log Y ≤ Y ^ (1 / 400 : ℝ) / (1 / 400) := h
      _ = 400 * Y ^ (1 / 400 : ℝ) := by
          rw [h2, div_eq_mul_inv, mul_comm]
          norm_num
  have hYsmall : Y ^ (1 / 400 : ℝ) ≤ Y ^ (1 / 200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hYp1 : (1 : ℝ) ≤ Y ^ (1 / 200 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have htotal : 96 * (4 * (harmonic N : ℝ) + 3) ≤ 1000000 * Y ^ (1 / 200 : ℝ) := by
    have : (harmonic N : ℝ) ≤ 1 + 800 * Y ^ (1 / 200 : ℝ) := by
      have := hlogY
      nlinarith [hYsmall, hYp, hlogN]
    nlinarith [hYp1]
  calc ∑ m ∈ rightInterval ε x, (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
        (1 + Y * |Real.log (w / (m : ℝ))|)
      ≤ 96 * ∑ m ∈ Finset.Icc 1 N, (1 + |w - (m : ℝ)|)⁻¹ := hstep1
    _ ≤ 96 * (4 * (harmonic N : ℝ) + 3) := by
        have := hH
        nlinarith [hH]
    _ ≤ 1000000 * Y ^ (1 / 200 : ℝ) := htotal

/-- `sieveQ` is at most `Y^(1/16)`. -/
private theorem sieveQ_le_sixteenth_aux {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  unfold sieveQ
  calc
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by norm_num)
    _ = (x ^ (11 / 20 + ε)) ^ ((1 / 16 : ℝ) - 1 / 10 ^ 5) := by
      rw [← Real.rpow_mul hY0]
      congr 1
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

/-- For `Y ≥ 6^16`, `6 Y^(1/8) ≤ Y`. -/
private theorem six_mul_eighth_le_aux {Y : ℝ} (hY : (6 : ℝ) ^ 16 ≤ Y) :
    6 * Y ^ (1 / 8 : ℝ) ≤ Y := by
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY
  have e : (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ := by norm_num
  have h1 : (6 : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hY (by norm_num : (0:ℝ) ≤ 1 / 16)
    rw [e, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
    rw [e]; exact this
  have h2 : Y ^ (1 / 16 : ℝ) ≤ Y ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have h3 : Y = Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : 0 ≤ Y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hY0 _
  calc 6 * Y ^ (1 / 8 : ℝ) ≤ Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) h4
    _ = Y := h3.symm

/-- Page 43 to 44, the window as a difference of steps: for `m > 0` and `y ≤ w`,
`[y ≤ m ≤ w] = [w/m ≥ 1] - [y/m > 1]`. -/
private theorem window_step {y w : ℝ} (hyw : y ≤ w) {m : ℝ} (hm : 0 < m) (a : ℂ) :
    (if y ≤ m ∧ m ≤ w then a else 0) =
      a * ((if 1 ≤ w / m then (1 : ℂ) else 0) - (if 1 < y / m then (1 : ℂ) else 0)) := by
  by_cases h1 : m ≤ w <;> by_cases h2 : m < y
  · have e1 : 1 ≤ w / m := (one_le_div hm).2 h1
    have e2 : 1 < y / m := (one_lt_div hm).2 h2
    simp [e1, e2, not_le.2 h2]
  · have e1 : 1 ≤ w / m := (one_le_div hm).2 h1
    have e2 : ¬ 1 < y / m := fun h => h2 ((one_lt_div hm).1 h)
    simp [e1, e2, not_lt.1 h2, h1]
  · exfalso; push_neg at h1; linarith
  · have e1 : ¬ 1 ≤ w / m := fun h => h1 ((one_le_div hm).1 h)
    have e2 : ¬ 1 < y / m := fun h => h2 ((one_lt_div hm).1 h)
    simp [e1, e2, h1]

/-- LEAF: page 43 to 44, proof of Lemma 29, the truncated Perron formula, class HARD.
P0069 Baker Harman Pintz 1997, "by [29] Lemma 3.19": for `y` in `[Y/2, 3Y]` the window sum
`Σ_{m ∈ J, y ≤ m ≤ y + yz} b(m) χ(m)` equals
`(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ) ((y+yz)^s - y^s)/s ds + O(Y^ε)`, with `G` the Dirichlet
polynomial of `b χ` over J. Written with `s = 1/2 + it`, `ds = i dt`. The error `O(Y^ε)` is
taken with `ε = 1/100`; it holds since `|b(m)| ≪ d(m)^B` by 3.1, so every coefficient is
`O(Y^(1/200))`, and the Perron error of Titchmarsh Lemma 3.19 at height `Y` is
`≪ max |b(m)| log Y`. CITED [29] Lemma 3.19. -/
theorem leaf_perron_window (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y →
          y ≤ 3 * x ^ (11 / 20 + ε) →
          ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
            ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
            K * (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := by
  obtain ⟨K2, hK2, C2, h2⟩ := log_sum_bound hε
  obtain ⟨K3, hK3, C3, h3⟩ := coeff_divisor b hε hb
  refine ⟨4 * K3 * K2, by positivity,
    max (max C2 C3) (max ((6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹)) 1), ?_⟩
  intro x hx q hq hqQ z hz1 hz2 χ y hy1 hy2
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx6 : (6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹) ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have ha : 0 < 11 / 20 + ε := by linarith
  have hY6 : (6 : ℝ) ^ 16 ≤ x ^ (11 / 20 + ε) := by
    have hCn : (0 : ℝ) ≤ ((6 : ℝ) ^ 16) ^ (((11 / 20 + ε))⁻¹) := by positivity
    have h := Real.rpow_le_rpow hCn hx6 ha.le
    have h2 : (((6 : ℝ) ^ 16) ^ (((11 / 20 + ε))⁻¹)) ^ (11 / 20 + ε) = (6 : ℝ) ^ 16 :=
      Real.rpow_inv_rpow (x := (6 : ℝ) ^ 16) (y := 11 / 20 + ε) (by positivity) ha.ne'
    rwa [h2] at h
  have hY : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by positivity) hY6
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY6
  have hQ := sieveQ_le_sixteenth_aux hY1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQr : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hQ1 : (1 : ℝ) ≤ sieveQ ε x := hq1.trans hqQr
  have hqQ0 : 0 < (q : ℝ) * sieveQ ε x := by positivity
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have h16 : (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) =
      (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  have h6qQ : 6 * q * (sieveQ ε x : ℝ) ≤ x ^ (11 / 20 + ε) := by
    have hQ0 : (0 : ℝ) ≤ sieveQ ε x := by positivity
    calc 6 * q * (sieveQ ε x : ℝ) ≤ 6 * ((x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) *
          (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ)) := by
          have := mul_le_mul (hqQr.trans hQ) hQ hQ0 (Real.rpow_nonneg hY.le _)
          nlinarith
      _ = 6 * (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by rw [h16]
      _ ≤ _ := six_mul_eighth_le_aux hY6
  have hz1' : z ≤ 1 := hz2.trans ((div_le_one hY).2 h6qQ)
  have hy0 : 0 < y := by linarith
  have hw1 : 0 < y + y * z := by nlinarith
  have hw1a : x ^ (11 / 20 + ε) / 2 ≤ y + y * z := by nlinarith
  have hw1b : y + y * z ≤ 6 * x ^ (11 / 20 + ε) := by nlinarith
  have hyw : y ≤ y + y * z := by nlinarith
  set J := rightInterval ε x with hJdef
  have hJ : ∀ m ∈ J, 1 ≤ m := fun m hm => rightInterval_one_le hm
  set a : ℕ → ℂ := fun m => (b x m : ℂ) * χ (m : ZMod q) with hadef
  set f : ℝ → ℕ → ℝ := fun w m =>
    (w / (m : ℝ)) ^ (1 / 2 : ℝ) /
      (1 + x ^ (11 / 20 + ε) * |Real.log (w / (m : ℝ))|) with hfdef
  have hsum1 : ∑ m ∈ J, f (y + y * z) m ≤ K2 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
    simpa only [hfdef] using h2 x hx2 (y + y * z) hw1a hw1b
  have hsum2 : ∑ m ∈ J, f y m ≤ K2 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
    simpa only [hfdef] using h2 x hx2 y (by linarith) (by linarith)
  have hW : (∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (b x m : ℂ) * χ (m : ZMod q)) =
      ∑ m ∈ J, a m * ((if 1 ≤ (y + y * z) / (m : ℝ) then (1 : ℂ) else 0) -
        (if 1 < y / (m : ℝ) then (1 : ℂ) else 0)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hJ m hm
    exact window_step hyw hm0 (a m)
  have hP := perron_sum_identity J hJ a (x ^ (11 / 20 + ε)) (y + y * z) y hw1 hy0
  have hS : ∀ m ∈ J, ‖a m‖ ≤ K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by
    intro m hm
    simp only [hadef, norm_mul]
    have hχ : ‖χ (m : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hbm : ‖(b x m : ℂ)‖ = |b x m| := Complex.norm_real _
    rw [hbm]
    calc |b x m| * ‖χ (m : ZMod q)‖ ≤ |b x m| * 1 :=
          mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h3 x hx3 m hm
  have hterm : ∀ (w : ℝ), 0 < w → ∀ m ∈ J, ∀ (H : Prop) [Decidable H],
      (1 < w / (m : ℝ) → H) → (w / (m : ℝ) < 1 → ¬H) →
      ‖(if H then (1 : ℂ) else 0) - perronI (w / m) (1 / 2) (x ^ (11 / 20 + ε))‖ ≤
        2 * f w m := by
    intro w hw m hm H _ hH1 hH2
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hJ m hm
    exact perron_term_bound (div_pos hw hm0) (by norm_num) hY H hH1 hH2
  have hR0 : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := Real.rpow_nonneg hY.le _
  have hR2 : (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) *
      (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) = (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  have hcollapse : ∑ m ∈ J, (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
        (2 * f (y + y * z) m + 2 * f y m)
      = 2 * (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
          ((∑ m ∈ J, f (y + y * z) m) + ∑ m ∈ J, f y m) := by
    rw [show (∑ m ∈ J, (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
          (2 * f (y + y * z) m + 2 * f y m))
        = ∑ m ∈ J, (2 * (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) * f (y + y * z) m +
            2 * (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) * f y m) from
      Finset.sum_congr rfl (fun m _ => by ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hW, hP, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ m ∈ J, ‖a m * (((if 1 ≤ (y + y * z) / (m : ℝ) then (1 : ℂ) else 0) -
          (if 1 < y / (m : ℝ) then (1 : ℂ) else 0)) -
          (perronI ((y + y * z) / m) (1 / 2) (x ^ (11 / 20 + ε)) -
            perronI (y / m) (1 / 2) (x ^ (11 / 20 + ε))))‖ := by
        refine le_of_eq_of_le ?_ (norm_sum_le _ _)
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ m ∈ J, (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
          (2 * f (y + y * z) m + 2 * f y m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hJ m hm
        rw [norm_mul]
        have e1 := hterm (y + y * z) hw1 m hm (1 ≤ (y + y * z) / (m : ℝ))
          (fun h => h.le) (fun h h' => absurd h' (not_le.2 h))
        have e2 := hterm y hy0 m hm (1 < y / (m : ℝ)) id
          (fun h h' => absurd h' (not_lt.2 h.le))
        have hsplit : ‖((if 1 ≤ (y + y * z) / (m : ℝ) then (1 : ℂ) else 0) -
            (if 1 < y / (m : ℝ) then (1 : ℂ) else 0)) -
            (perronI ((y + y * z) / m) (1 / 2) (x ^ (11 / 20 + ε)) -
              perronI (y / m) (1 / 2) (x ^ (11 / 20 + ε)))‖ ≤
            2 * f (y + y * z) m + 2 * f y m := by
          calc _ = ‖((if 1 ≤ (y + y * z) / (m : ℝ) then (1 : ℂ) else 0) -
                perronI ((y + y * z) / m) (1 / 2) (x ^ (11 / 20 + ε))) -
              ((if 1 < y / (m : ℝ) then (1 : ℂ) else 0) -
                perronI (y / m) (1 / 2) (x ^ (11 / 20 + ε)))‖ := by
                congr 1; ring
            _ ≤ _ := norm_sub_le _ _
            _ ≤ _ := add_le_add e1 e2
        exact mul_le_mul (hS m hm) hsplit (norm_nonneg _) (by positivity)
    _ = 2 * (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
          ((∑ m ∈ J, f (y + y * z) m) + ∑ m ∈ J, f y m) := hcollapse
    _ ≤ 2 * (K3 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) *
          (K2 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) +
            K2 * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) := by
        gcongr
    _ = 4 * K3 * K2 * ((x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) *
          (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ)) := by ring
    _ = _ := by rw [hR2]

/-- `y^(1/2+it) = √y * exp(i t log y)` for `y > 0`. -/
private lemma cpow_half_add_it {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
      = (Real.sqrt y : ℂ) * Complex.exp (((t : ℂ) * (Real.log y : ℂ)) * I) := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_add (1 / 2 : ℂ) ((t : ℂ) * I) hyc]
  have h1 : (y : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt y : ℂ) := by
    have h := (Complex.ofReal_cpow (x := y) hy.le (1 / 2 : ℝ)).symm
    rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num] at h
    rw [Real.sqrt_eq_rpow]
    exact h
  have h2 : (y : ℂ) ^ ((t : ℂ) * I)
      = Complex.exp (((t : ℂ) * (Real.log y : ℂ)) * I) := by
    rw [Complex.cpow_def_of_ne_zero hyc, ← Complex.ofReal_log hy.le]
    congr 1
    ring
  rw [h1, h2]

/-- The Fourier character at `t a / 2π` is `exp (i t a)`. -/
private lemma fourierChar_eq_exp (t a : ℝ) :
    (Real.fourierChar (t * a / (2 * Real.pi)) : ℂ)
      = Complex.exp (((t : ℂ) * (a : ℂ)) * I) := by
  have hq : 2 * Real.pi * (t * a / (2 * Real.pi)) = t * a := by
    field_simp
  rw [Real.fourierChar_apply, hq, Complex.ofReal_mul]

/-- The indicator of an interval times a continuous function is `L¹` and `L²`. -/
private lemma indicator_memLp (g : ℝ → ℂ) (hg : Continuous g) (T : ℝ) :
    Integrable (Set.indicator (Set.Ioc (-T) T) g) ∧
      MemLp (Set.indicator (Set.Ioc (-T) T) g) 2 := by
  have hms : MeasurableSet (Set.Ioc (-T) T) := measurableSet_Ioc
  have hIO : IntegrableOn g (Set.Ioc (-T) T) :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hg.continuousOn).mono_set
      Set.Ioc_subset_Icc_self
  refine ⟨hIO.integrable_indicator hms, ?_⟩
  have haesm : AEStronglyMeasurable (Set.indicator (Set.Ioc (-T) T) g) :=
    hg.aestronglyMeasurable.indicator hms
  refine (memLp_two_iff_integrable_sq_norm haesm).2 ?_
  have hEq : (fun t => ‖Set.indicator (Set.Ioc (-T) T) g t‖ ^ 2)
      = Set.indicator (Set.Ioc (-T) T) (fun t => ‖g t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (-T) T <;> simp [ht]
  rw [hEq]
  exact ((ContinuousOn.integrableOn_compact isCompact_Icc (hg.norm.pow 2).continuousOn).mono_set
    Set.Ioc_subset_Icc_self).integrable_indicator hms

/-- Plancherel for the interval-restricted function. -/
private lemma window_plancherel (g : ℝ → ℂ) (hg : Continuous g) {T : ℝ} (hT : 0 ≤ T) :
    ∫ u : ℝ, ‖(FourierTransform.fourier (Set.indicator (Set.Ioc (-T) T) g) : ℝ → ℂ) u‖ ^ 2
      = ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨hInt, hmem⟩ := indicator_memLp g hg T
  rw [LeanLab.ExceptionalSet.WindowParseval264.integral_norm_sq_fourier
    (Set.indicator (Set.Ioc (-T) T) g) hInt hmem]
  have hms : MeasurableSet (Set.Ioc (-T) T) := measurableSet_Ioc
  have hEq : (fun x => ‖Set.indicator (Set.Ioc (-T) T) g x‖ ^ 2)
      = Set.indicator (Set.Ioc (-T) T) (fun t => ‖g t‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (-T) T <;> simp [ht]
  rw [hEq, MeasureTheory.integral_indicator hms,
    ← intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)]

/-- The main mean-square bound, with the `y`-variable as in the leaf. -/
private lemma plancherel_window_y (g : ℝ → ℂ) (hg : Continuous g) {T Y : ℝ} (hT : 0 ≤ T)
    (hY : 0 < Y) :
    ∫ y in (Y / 2)..(3 * Y),
        ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ 18 * Real.pi * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  obtain ⟨hInt, hmem⟩ := indicator_memLp g hg T
  set f : ℝ → ℂ := Set.indicator (Set.Ioc (-T) T) g with hf
  set Ψ : ℝ → ℝ := fun u => ‖(FourierTransform.fourier f : ℝ → ℂ) u‖ ^ 2 with hΨ
  have hFcont : Continuous (FourierTransform.fourier f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hInt
  have hΨcont : Continuous Ψ := by
    rw [hΨ]
    exact (hFcont.norm).pow 2
  have hΨnn : ∀ u : ℝ, 0 ≤ Ψ u := by intro u; rw [hΨ]; positivity
  -- the pointwise identity
  have hpt : ∀ y : ℝ, 0 < y →
      ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        = y * Ψ (-(Real.log y) / (2 * Real.pi)) := by
    intro y hy
    have harg : ∀ t : ℝ, -(inner ℝ t (-(Real.log y) / (2 * Real.pi)))
        = t * Real.log y / (2 * Real.pi) := by
      intro t; rw [Real.inner_apply]; ring
    have hG : (FourierTransform.fourier f : ℝ → ℂ) (-(Real.log y) / (2 * Real.pi))
        = ∫ t in (-T)..T, g t * Complex.exp (((t : ℂ) * (Real.log y : ℂ)) * I) := by
      rw [Real.fourier_eq]
      simp only [Circle.smul_def, smul_eq_mul]
      have hfun : (fun t : ℝ => (Real.fourierChar (-inner ℝ t (-(Real.log y) / (2 * Real.pi)))
            : ℂ) * Set.indicator (Set.Ioc (-T) T) g t)
          = (fun t : ℝ => Set.indicator (Set.Ioc (-T) T)
              (fun t => g t * Complex.exp (((t : ℂ) * (Real.log y : ℂ)) * I)) t) := by
        funext t
        rw [harg t, fourierChar_eq_exp]
        by_cases ht : t ∈ Set.Ioc (-T) T
        · simp only [Set.indicator_of_mem ht]
          ring
        · simp only [Set.indicator_of_notMem ht, mul_zero]
      rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioc,
        intervalIntegral.integral_of_le (a := -T) (b := T) (by linarith)]
    have hFy : (∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))
        = (Real.sqrt y : ℂ) *
            (FourierTransform.fourier f : ℝ → ℂ) (-(Real.log y) / (2 * Real.pi)) := by
      rw [hG, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [cpow_half_add_it hy t]
      ring
    rw [hFy, norm_mul, mul_pow]
    have hsq : ‖(Real.sqrt y : ℂ)‖ ^ 2 = y := by
      rw [Complex.sq_norm, Complex.normSq_ofReal, Real.mul_self_sqrt hy.le]
    rw [hsq, hΨ]
  -- substitution `y = exp u`
  set a : ℝ := Real.log (Y / 2) with ha
  set b : ℝ := Real.log (3 * Y) with hb
  have hab : a ≤ b := by
    rw [ha, hb]; exact Real.log_le_log (by linarith) (by linarith)
  have hY2 : (0 : ℝ) < Y / 2 := by linarith
  have hY3 : (0 : ℝ) < 3 * Y := by linarith
  have hexpa : Real.exp a = Y / 2 := Real.exp_log hY2
  have hexpb : Real.exp b = 3 * Y := Real.exp_log hY3
  have hlogcont : ContinuousOn (fun y : ℝ => Real.log y) (Real.exp '' Set.uIcc a b) :=
    Real.continuousOn_log.mono (by
      rintro _ ⟨x, -, rfl⟩
      simp)
  have hsub_cont : ContinuousOn (fun y : ℝ => y * Ψ (-(Real.log y) / (2 * Real.pi)))
      (Real.exp '' Set.uIcc a b) :=
    continuous_id.continuousOn.mul
      (hΨcont.comp_continuousOn (hlogcont.neg.div_const _))
  have hsubst : ∫ y in (Y / 2)..(3 * Y),
        ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
      = ∫ u in a..b, Real.exp (2 * u) * Ψ (-(u) / (2 * Real.pi)) := by
    have h1 : ∫ y in (Y / 2)..(3 * Y),
        ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
        = ∫ y in (Y / 2)..(3 * Y), y * Ψ (-(Real.log y) / (2 * Real.pi)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      simp only [Set.uIcc_of_le (by linarith : Y / 2 ≤ 3 * Y), Set.mem_Icc] at hy
      exact hpt y (by linarith [hy.1])
    rw [h1]
    have key := intervalIntegral.integral_comp_mul_deriv'
      (a := a) (b := b) (f := Real.exp) (f' := Real.exp)
      (g := fun y : ℝ => y * Ψ (-(Real.log y) / (2 * Real.pi)))
      (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hsub_cont
    simp only [Function.comp] at key
    rw [hexpa, hexpb] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [Real.log_exp]
    have e2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
      rw [show (2 : ℝ) * u = u + u by ring, Real.exp_add]
    rw [e2]
    ring
  -- bound the exponential weight
  have hstep1 : ∫ u in a..b, Real.exp (2 * u) * Ψ (-(u) / (2 * Real.pi))
      ≤ ∫ u in a..b, (9 * Y ^ 2) * Ψ (-(u) / (2 * Real.pi)) := by
    have hc1 : Continuous fun u : ℝ => Real.exp (2 * u) * Ψ (-(u) / (2 * Real.pi)) :=
      (Real.continuous_exp.comp (by fun_prop)).mul (hΨcont.comp (by fun_prop))
    have hc2 : Continuous fun u : ℝ => (9 * Y ^ 2) * Ψ (-(u) / (2 * Real.pi)) :=
      continuous_const.mul (hΨcont.comp (by fun_prop))
    apply intervalIntegral.integral_mono_on hab (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)
    intro u hu
    have h1 : Real.exp u ≤ 3 * Y := by
      calc Real.exp u ≤ Real.exp b := Real.exp_le_exp.mpr hu.2
        _ = 3 * Y := hexpb
    have h2 : Real.exp (2 * u) = (Real.exp u) ^ 2 := by
      rw [show (2 : ℝ) * u = u + u by ring, Real.exp_add]
      ring
    rw [h2]
    have h3 : Real.exp u * Real.exp u ≤ (3 * Y) * (3 * Y) :=
      mul_self_le_mul_self (by positivity) h1
    have h9 : (3 * Y) * (3 * Y) = 9 * Y ^ 2 := by ring
    rw [h9] at h3
    nlinarith [h3, hΨnn (-(u) / (2 * Real.pi))]
  -- integrability of the rescaled Ψ
  have hΨint : Integrable fun u : ℝ => Ψ (-(u) / (2 * Real.pi)) := by
    have hFmem : MemLp (FourierTransform.fourier f : ℝ → ℂ) 2 :=
      MemLp.ae_eq (LeanLab.ExceptionalSet.WindowParseval264.fourierIntegral_ae_eq
        f hInt hmem).symm (Lp.memLp _)
    have h0 : Integrable Ψ :=
      (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hR : (-(2 * Real.pi)⁻¹) ≠ 0 := by simp
    have hcomp : Integrable fun u : ℝ => Ψ (-(2 * Real.pi)⁻¹ * u) :=
      h0.comp_mul_left' (R := -(2 * Real.pi)⁻¹) hR
    have heq : (fun u : ℝ => Ψ (-(u) / (2 * Real.pi)))
        = (fun u : ℝ => Ψ (-(2 * Real.pi)⁻¹ * u)) := by
      funext u
      congr 1
      field_simp
    rw [heq]
    exact hcomp
  -- monotonicity: the interval is below the line
  have hmono : ∫ u in a..b, Ψ (-(u) / (2 * Real.pi))
      ≤ ∫ u : ℝ, Ψ (-(u) / (2 * Real.pi)) := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_le_integral hΨint
      (Filter.Eventually.of_forall fun u => hΨnn (-(u) / (2 * Real.pi)))
  have hrescale : ∫ u : ℝ, Ψ (-(u) / (2 * Real.pi))
      = 2 * Real.pi * ∫ u : ℝ, Ψ u := by
    have h := MeasureTheory.Measure.integral_comp_mul_left (g := Ψ) (-(2 * Real.pi)⁻¹)
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have ha : |(-(2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
      rw [inv_neg, inv_inv, abs_neg, abs_of_pos hpi]
    rw [ha, smul_eq_mul] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with u
    congr 1
    field_simp
  have hplan : ∫ u : ℝ, Ψ u = ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
    rw [hΨ]
    exact window_plancherel g hg hT
  calc ∫ y in (Y / 2)..(3 * Y),
        ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
      = ∫ u in a..b, Real.exp (2 * u) * Ψ (-(u) / (2 * Real.pi)) := hsubst
    _ ≤ ∫ u in a..b, (9 * Y ^ 2) * Ψ (-(u) / (2 * Real.pi)) := hstep1
    _ = (9 * Y ^ 2) * ∫ u in a..b, Ψ (-(u) / (2 * Real.pi)) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ (9 * Y ^ 2) * ∫ u : ℝ, Ψ (-(u) / (2 * Real.pi)) := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (9 * Y ^ 2) * (2 * Real.pi * ∫ u : ℝ, Ψ u) := by rw [hrescale]
    _ = (9 * Y ^ 2) * (2 * Real.pi * ∫ t in (-T)..T, ‖g t‖ ^ 2) := by rw [hplan]
    _ = 18 * Real.pi * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by ring

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2, class HARD. P0069 Baker
Harman Pintz 1997, "By a variant of [8], Lemma 2,
`∫_{Y/2}^{3Y} |∫_T^{T'} g(t) y^(it) dt|^2 dy ≪ Y L ∫_T^{T'} |g(t)|^2 dt` whenever `g` is
continuous". Here with the factor `y^(1/2)` of `y^s`, `s = 1/2 + it`, kept inside, so the
bound is `Y^2` instead of `Y`, since `|y^(1/2)|^2 ≤ 3Y`, and with the `t` range `[-T, T]` in
which the paper applies it. The printed variant has a factor `L`; this leaf takes the form
without `L`, which the lab statement of `leaf_char_nonprincipal` needs and which holds by
Plancherel after `y = e^u`, with an absolute constant: QUESTION 1 of the note. CITED [8]
Lemma 2, Gallagher 1970. -/
theorem leaf_mellin_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  refine ⟨18 * Real.pi, by positivity, ?_⟩
  intro Y hY T hT g hg
  exact plancherel_window_y g hg hT hY

/-- Page 3, the definition of Q: `Q ≤ Y^(1/16)` when `Y ≥ 1`. -/
theorem sieveQ_le_sixteenth {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  unfold sieveQ
  calc
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by norm_num)
    _ = (x ^ (11 / 20 + ε)) ^ ((1 / 16 : ℝ) - 1 / 10 ^ 5) := by
      rw [← Real.rpow_mul hY0]
      congr 1
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

/-- For `Y ≥ 6^16`, `6 Y^(1/8) ≤ Y`. -/
theorem six_mul_eighth_le {Y : ℝ} (hY : (6 : ℝ) ^ 16 ≤ Y) :
    6 * Y ^ (1 / 8 : ℝ) ≤ Y := by
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY
  have e : (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ := by norm_num
  have h1 : (6 : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hY (by norm_num : (0:ℝ) ≤ 1 / 16)
    rw [e, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
    rw [e]; exact this
  have h2 : Y ^ (1 / 16 : ℝ) ≤ Y ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have h3 : Y = Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : 0 ≤ Y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hY0 _
  calc 6 * Y ^ (1 / 8 : ℝ) ≤ Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) h4
    _ = Y := h3.symm


/-- Page 44, proof of Lemma 29, the step "the left hand side of (5.3) is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, where we used
`|((1+z)^(1/2+it) - 1)/(1/2+it)|^2 ≪ 1/(T2^2 + t^2)` in the first step", for one character.
PROVED from the LEAF `leaf_mellin_mean_value` and the kernel bound
`DQLeaf518Split.lemma29_ineq_six`: `(y+yz)^s - y^s = y^s ((1+z)^s - 1)`, and `z ≤ 1` for
large `x` since `qQ ≤ Q^2 ≤ Y^(1/8)`. -/
theorem leaf_perron_mean_square (b : ℝ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
  obtain ⟨K, hK, hgen⟩ := leaf_mellin_mean_value
  set c : ℝ := ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨K * (c * 324), by positivity, max ((6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹)) 1,
    fun x hx q hq hqQ z hz1 hz2 χ => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have ha : 0 < 11 / 20 + ε := by linarith
  have hY6 : (6 : ℝ) ^ 16 ≤ x ^ (11 / 20 + ε) := by
    have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_left _ _) hx) ha.le
    rwa [Real.rpow_inv_rpow (by positivity) ha.ne'] at h
  have hY : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by positivity) hY6
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY6
  have hQ := sieveQ_le_sixteenth hY1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQr : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hQ1 : (1 : ℝ) ≤ sieveQ ε x := hq1.trans hqQr
  have hqQ0 : 0 < (q : ℝ) * sieveQ ε x := by positivity
  have hT2 : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) := div_pos hY hqQ0
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have h16 : (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) =
      (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  have h6qQ : 6 * q * (sieveQ ε x : ℝ) ≤ x ^ (11 / 20 + ε) := by
    have hQ0 : (0 : ℝ) ≤ sieveQ ε x := by positivity
    calc 6 * q * (sieveQ ε x : ℝ) ≤ 6 * ((x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) *
          (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ)) := by
          have := mul_le_mul (hqQr.trans hQ) hQ hQ0 (Real.rpow_nonneg hY.le _)
          nlinarith
      _ = 6 * (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by rw [h16]
      _ ≤ _ := six_mul_eighth_le hY6
  have hz1' : z ≤ 1 := hz2.trans ((div_le_one hY).2 h6qQ)
  have hzT : z ≤ 6 / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) := by
    rw [div_div_eq_mul_div]
    calc z ≤ _ := hz2
      _ = _ := by ring
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have h1zne : (((1 + z : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h1z.ne'
  -- the Dirichlet polynomial and the weight `g`
  have hs : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hG := DQLeaf518Split.dirichlet_poly_continuous (rightInterval ε x)
    (fun m => (b x m : ℂ) * χ (m : ZMod q))
  have hc1 : Continuous fun t : ℝ => (((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hs.const_cpow (Or.inl h1zne)
  have hgc : Continuous fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
        ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) :=
    continuous_const.mul ((hG.mul (hc1.sub continuous_const)).div hs
      DQLeaf518Split.half_line_ne_zero)
  have hA := hgen (x ^ (11 / 20 + ε)) hY (x ^ (11 / 20 + ε)) hY.le _ hgc
  -- step A: rewrite the Perron integral
  have hEq : ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
              ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
                ((1 / 2 : ℂ) + (t : ℂ) * I)) *
          (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      linarith [hy.1]
    rw [← intervalIntegral.integral_const_mul]
    congr 2
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hm : ((y + y * z : ℝ) : ℂ) = ((y : ℝ) : ℂ) * (((1 + z : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hm, Complex.mul_cpow_ofReal_nonneg hy0 h1z.le]
    ring
  -- step C: the kernel bound
  have hk : ∀ t : ℝ, ‖(((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 /
      ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2 ≤
        324 / ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
    intro t
    have h := DQLeaf518Split.lemma29_ineq_six (t := t) hz0 hz1' hT2 hzT
    rw [Complex.cpow_def_of_ne_zero h1zne, ← Complex.ofReal_log h1z.le,
      mul_comm (((Real.log (1 + z)) : ℝ) : ℂ)]
    exact h
  have hRc : Continuous fun t : ℝ =>
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
    (hG.norm.pow 2).div (by fun_prop) fun t => by positivity
  have hC : ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
        ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
            ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
              ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
      ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), (c * 324) *
        (‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) ((hgc.norm.pow 2).intervalIntegrable _ _)
      ((continuous_const.mul hRc).intervalIntegrable _ _) fun t _ => ?_
    have hD : 0 < (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2 := by positivity
    rw [norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow, ← hc]
    have hG0 : 0 ≤ ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by positivity
    calc _ = c * ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          (‖(((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 /
            ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2) := by ring
      _ ≤ c * ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          (324 / ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (hk t) (mul_nonneg hc0 hG0)
      _ = _ := by ring
  rw [intervalIntegral.integral_const_mul] at hC
  rw [hEq]
  calc _ ≤ _ := hA
    _ ≤ K * (x ^ (11 / 20 + ε)) ^ 2 * ((c * 324) * ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
        ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- Page 44, the tacit triangle step: `|a|^2 ≤ 2 |b|^2 + 2 |a - b|^2`. -/
theorem norm_sq_le_two_mul (a c : ℂ) {E : ℝ} (h : ‖a - c‖ ≤ E) :
    ‖a‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * E ^ 2 := by
  have h1 : ‖a‖ ≤ ‖c‖ + ‖a - c‖ := by
    calc ‖a‖ = ‖c + (a - c)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have h0 : 0 ≤ ‖a - c‖ := norm_nonneg _
  have hc : 0 ≤ ‖c‖ := norm_nonneg _
  have h2 : ‖a‖ ≤ ‖c‖ + E := h1.trans (by linarith)
  have h3 : 0 ≤ ‖a‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖c‖ - E), mul_le_mul h2 h2 h3 (by linarith)]

/-- PROVED from the two LEAFs: exactly the statement of
`Prep1121LowExc.leaf_char_nonprincipal`, P0069 pages 43 and 44, the case `χ ∈ F`. Here
`δχ = 0`, the window sum is the Perron integral plus `O(Y^(1/100))` pointwise, and the square
of the error integrated over `[Y/2, 3Y]` is `(5Y/2) Y^(1/50)` times a constant. -/
theorem leaf_char_nonprincipal_of_leaves (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  obtain ⟨K1, hK1, C1, h1⟩ := leaf_perron_window b hε hb
  obtain ⟨K2, hK2, C2, h2⟩ := leaf_perron_mean_square b hε
  refine ⟨2 * K2 + 5 * K1 ^ 2, by positivity, max (max C1 C2) 1,
    fun x hx q hq hqQ z hz1 hz2 χ hχ => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hδ : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  -- integrability of the left integrand
  have hS := DQLeaf518Split.leaf_lemma29_integrable b ε x hx3 q χ z hz0
  simp only [hδ, zero_mul, sub_zero] at hS ⊢
  -- integrability of the Perron integral
  have hP := DQLeaf518Split.lemma29_integrable_aux (rightInterval ε x) (fun _ => 0)
    (fun m => (b x m : ℂ) * χ (m : ZMod q)) 1 (((2 * Real.pi : ℝ) : ℂ)⁻¹)
    (a := x ^ (11 / 20 + ε) / 2) (b := 3 * x ^ (11 / 20 + ε)) (T := x ^ (11 / 20 + ε))
    (z := z) (by linarith) hab hY.le hz0
  simp only [Finset.sum_const_zero, zero_sub, one_mul, norm_neg] at hP
  have hM := h2 x hx2 q hq hqQ z hz1 hz2 χ
  set Y := x ^ (11 / 20 + ε) with hYdef
  set E := K1 * Y ^ (1 / 100 : ℝ) with hE
  have hpt : ∀ y ∈ Set.Icc (Y / 2) (3 * Y),
      ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), (b x m : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
        2 * ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Y)..Y,
            (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          2 * E ^ 2 := fun y hy =>
    norm_sq_le_two_mul _ _ (h1 x hx1 q hq hqQ z hz1 hz2 χ y hy.1 hy.2)
  have hmono := intervalIntegral.integral_mono_on hab hS
    ((hP.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add (hP.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hI0 : 0 ≤ ∫ t in (-Y)..Y,
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
  have hR2 : (Y ^ (1 / 100 : ℝ)) ^ 2 = Y ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num
  have hE2 : E ^ 2 = K1 ^ 2 * Y ^ (1 / 50 : ℝ) := by
    rw [hE, mul_pow, hR2]
  have hR0 : 0 ≤ Y ^ (1 / 50 : ℝ) := Real.rpow_nonneg hY.le _
  rw [hE2] at hmono
  have hY2 : 0 ≤ Y ^ 2 := sq_nonneg Y
  calc _ ≤ _ := hmono
    _ ≤ 2 * (K2 * Y ^ 2 * (∫ t in (-Y)..Y,
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2))) +
        (3 * Y - Y / 2) * (2 * (K1 ^ 2 * Y ^ (1 / 50 : ℝ))) := by
      linarith [hM]
    _ ≤ _ := by
      have hK1s : 0 ≤ K1 ^ 2 := sq_nonneg K1
      have hA : 0 ≤ Y ^ 2 * (∫ t in (-Y)..Y,
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := mul_nonneg hY2 hI0
      have hB : 0 ≤ Y * Y ^ (1 / 50 : ℝ) := mul_nonneg hY.le hR0
      nlinarith [mul_nonneg hK2 hB, mul_nonneg hK1s hA]

/-- Twin check: the assembly has exactly the type of the open LEAF. -/
theorem leaf_char_nonprincipal_split_twin :
    type_of% @Prep1121LowExc.leaf_char_nonprincipal :=
  @leaf_char_nonprincipal_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP
