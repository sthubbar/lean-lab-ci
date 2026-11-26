import LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelectedDecisions

/-!
# Split of `Lemma2NoExcBP` into the displays of Montgomery and Vaughan 1975

Burst burst-20261122, unit P1122-0119, run by a Claude cloud session.

Source P0082, Brüdern and Perelli 1998, page 358 Lemma 2, whose whole proof is
"Combine (6.17) and (7.1) of Montgomery & Vaughan". Source P0015, Montgomery and Vaughan,
The exceptional set in Goldbach's problem, Acta Arith. 27 (1975) 353-370, pages 355 to 366,
read from the page images of `papers/P0015.pdf`.

Notation of P0015 section 2: `P = X^{6δ}`, `Q = X^{1-6δ}`, so `1/(qQ) = P/(qX)`; the major arc
`𝔐(q,a) = [a/q - 1/(qQ), a/q + 1/(qQ)]` for `1 ≤ a ≤ q ≤ P`, `(a,q) = 1`. P0082 page 357 says its
`R₁(m)` "coincides exactly with the quantity R₁(m) used by Montgomery & Vaughan"; the lab's
`U1539.R1` is that integral, over `N ∩ [0,1]`, which equals the integral over MV's union by
periodicity.

Structure.
* LEAF `mv_remainder_66_68`: displays (6.1) to (6.9), the remainder of the major arc expansion.
* LEAF `mv_arc_main_611`: display (6.11) for one modulus.
* LEAF `mv_truncation_613`: display (6.13).
* LEAF `mv_singular_series_616`: display (6.16), the series equals the product.
* LEAF `mv_tail_614`: display (6.14).
* LEAF `mv_gallagher_lemma42_step`: the first display of section 7, from Lemma 4.2.
* LEAF `mv_gallagher_lemma43`: Lemma 4.3, Gallagher's Theorem 7, run with zero free constant `a`.
* PROVED from the leaves: `mv_617`, display (6.17); `mv_71`, display (7.1);
  `lemma2NoExcSmallDelta_of_leaves`, P0082 Lemma 2 for small `δ`.
* PROVED sorry free: `lemma2NoExcSmallDelta_of_BP` and `leaf_absent_selected_of_small`, which gives
  the exact type of `Decomp559b.leaf_absent_selected` from the weaker named hypothesis
  `Lemma2NoExcSmallDelta`.

Why the twin `Lemma2NoExcSmallDelta`. `Lemma2NoExcBP` asks for `c₁, K` uniform over every
`0 < δ < 1/100`. P0082 page 357 does state that range, but MV prove (6.17) with (7.1) only through
Lemma 4.3, which needs `P ≤ N^{c₄}` with a small absolute `c₄`, and MV take `δ` "eventually a small
positive absolute constant", P0015 page 354. The leaf only ever uses small `δ`, so the twin asks for
the bound below some `δ₁ > 0`. See the notes file for the QUESTION.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 eC nu)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected
  (singularSeries NoExceptionalReal Lemma2NoExcBP SingularSeriesEvenLowerBP exp_neg_le_inv
    noExceptionalReal_of_selected_one)

/-! ### Definitions, each a display of P0015 -/

/-- P0015 page 361: `T(η) = Σ_{P<n≤X} e(nη)`. -/
noncomputable def T (P X η : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * n)

/-- P0015 display (2.3): `S(χ,η) = Σ_{P<p≤X} (log p) χ(p) e(pη)`. -/
noncomputable def Schi {q : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, (Real.log p : ℂ) * χ (p : ZMod q) * eC (η * p)

open Classical in
/-- P0015 page 361, the line before (6.2): `S(χ₀,η) = T(η) + W(χ₀,η)` and `S(χ,η) = W(χ,η)` for
`χ ≠ χ₀`. The exceptional modification `(6.2~)` is not made, so this `W` is the one of (6.2). -/
noncomputable def Wchi {q : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  Schi P X χ η - if χ = 1 then T P X η else 0

/-- P0015 display (6.5), with `1/(rQ) = P/(rX)`:
`W(χ) = (∫_{-1/rQ}^{1/rQ} |W(χ,η)|² dη)^{1/2}` for `χ` of modulus `r`. -/
noncomputable def Wnorm {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) : ℝ :=
  Real.sqrt (∫ η in (-(P / (r * X)))..(P / (r * X)), ‖Wchi P X χ η‖ ^ 2)

/-- P0015 display (6.9): `W = Σ_{q≤P} Σ*_χ W(χ)`, the inner sum over primitive `χ` mod `q`. -/
noncomputable def mvW (P X : ℝ) : ℝ :=
  ∑ r ∈ Icc 1 ⌊P⌋₊, ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Wnorm P X χ.1

/-- Ramanujan's sum `c_q(m) = Σ'_{h mod q} e(hm/q)`, P0015 page 354. -/
noncomputable def ramanujan (q : ℕ) (m : ℤ) : ℂ :=
  ∑ h ∈ (range q).filter (fun h => Nat.Coprime h q), eC ((h : ℝ) * m / q)

/-- The coefficient `μ(q)² φ(q)⁻² c_q(-n)` of the first term of P0015 display (6.4). -/
noncomputable def mainWeight (q n : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) *
    ramanujan q (-(n : ℤ))

/-- The integral `∫_{-1/qQ}^{1/qQ} T(η)² e(-nη) dη` of the first term of P0015 display (6.4). -/
noncomputable def arcIntegral (P X : ℝ) (q n : ℕ) : ℂ :=
  ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η ^ 2 * eC (-(η * n))

open Classical in
/-- The sum `Σ^#_{x-h<n≤x}` of P0015 Lemma 4.3, restricted to `P < n ≤ X` as in the first display
of section 7: `χ(p) log p` at primes, minus `1` at every integer when `χ` is principal. These are
the coefficients of `W(χ,η)`. -/
noncomputable def sharpSum {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (x h : ℝ) : ℂ :=
  ∑ n ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter (fun n : ℕ => x - h < (n : ℝ) ∧ (n : ℝ) ≤ x),
    ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) - if χ = 1 then 1 else 0)

/-! ### Private helpers for the major arc leaves -/

private lemma eC_zero : eC 0 = 1 := by
  simp [eC]

private lemma eC_add_real (a b : ℝ) : eC a * eC b = eC (a + b) := by
  simp only [eC, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_eC_real (x : ℝ) : ‖eC x‖ = 1 := by
  rw [show eC x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) from by
    simp only [eC]
    congr 1
    push_cast
    ring]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private lemma eC_nat_mul (η : ℝ) (k : ℕ) : eC (η * (k : ℝ)) = eC η ^ k := by
  induction k with
  | zero => simp [eC_zero]
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc, mul_add, mul_one, ← eC_add_real, ih, pow_succ]

private lemma re_eC (η : ℝ) : (eC η).re = Real.cos (2 * Real.pi * η) := by
  rw [show eC η = Complex.exp (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) from by
    simp only [eC]; congr 1; push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

private lemma im_eC (η : ℝ) : (eC η).im = Real.sin (2 * Real.pi * η) := by
  rw [show eC η = Complex.exp (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) from by
    simp only [eC]; congr 1; push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_im]

private lemma norm_one_sub_eC (η : ℝ) :
    ‖1 - eC η‖ = 2 * |Real.sin (Real.pi * η)| := by
  have hsq : ‖1 - eC η‖ ^ 2 = (2 * |Real.sin (Real.pi * η)|) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    rw [re_eC, im_eC]
    have hcos : Real.cos (2 * Real.pi * η) = 2 * Real.cos (Real.pi * η) ^ 2 - 1 := by
      rw [show (2:ℝ) * Real.pi * η = 2 * (Real.pi * η) by ring, Real.cos_two_mul]
    have hsin : Real.sin (2 * Real.pi * η) = 2 * Real.sin (Real.pi * η) * Real.cos (Real.pi * η) := by
      rw [show (2:ℝ) * Real.pi * η = 2 * (Real.pi * η) by ring, Real.sin_two_mul]
    have hsq2 : (2 * |Real.sin (Real.pi * η)|) ^ 2 = 4 * Real.sin (Real.pi * η) ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [hsq2, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * η)]
  have h1 : (0:ℝ) ≤ ‖1 - eC η‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ 2 * |Real.sin (Real.pi * η)| := by positivity
  nlinarith [hsq, h1, h2]

private lemma integral_exp_mul_complex (c : ℂ) (hc : c ≠ 0) (A B : ℝ) :
    ∫ x in A..B, Complex.exp (c * (x : ℂ)) =
      (Complex.exp (c * (B : ℂ)) - Complex.exp (c * (A : ℂ))) / c := by
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)) / c) (Complex.exp (c * (x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) (c * 1) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
        (Complex.exp (c * (x : ℂ)) * (c * 1)) x := h1.cexp
    have h3 := h2.div_const c
    rw [mul_one] at h3
    convert h3 using 1
    exact (mul_div_cancel_right₀ _ hc).symm
  have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ))) MeasureTheory.volume A B :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (c * (x : ℂ))).intervalIntegrable A B
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [sub_div]

/-- Orthogonality of the exponential sum over a full period, for an integer frequency. -/
private lemma integral_eC_int (m : ℤ) :
    ∫ η in (-1/2 : ℝ)..(1/2), eC (η * (m : ℝ)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [eC]
    norm_num
  · have hc : ((2 * Real.pi * Complex.I) * (m : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hm
    have hfun : ∀ η : ℝ, eC (η * (m : ℝ)) =
        Complex.exp (((2 * Real.pi * Complex.I) * (m : ℂ)) * (η : ℂ)) := by
      intro η
      simp only [eC]
      congr 1
      push_cast
      ring
    simp only [hfun]
    rw [if_neg hm, integral_exp_mul_complex _ hc]
    have hz1 : Complex.exp (((2 * Real.pi * Complex.I) * (m : ℂ)) * ((1/2 : ℝ) : ℂ)) =
        Complex.exp (Real.pi * Complex.I * (m : ℂ)) := by
      congr 1
      push_cast
      ring
    have hz2 : Complex.exp (((2 * Real.pi * Complex.I) * (m : ℂ)) * ((-1/2 : ℝ) : ℂ)) =
        (Complex.exp (Real.pi * Complex.I * (m : ℂ)))⁻¹ := by
      rw [show ((2 * Real.pi * Complex.I) * (m : ℂ)) * ((-1/2 : ℝ) : ℂ) =
        -(Real.pi * Complex.I * (m : ℂ)) by push_cast; ring, Complex.exp_neg]
    rw [hz1, hz2]
    have hzz : Complex.exp (Real.pi * Complex.I * (m : ℂ)) *
        Complex.exp (Real.pi * Complex.I * (m : ℂ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_int_mul_two_pi_mul_I m]
      congr 1
      push_cast
      ring
    have hinv : (Complex.exp (Real.pi * Complex.I * (m : ℂ)))⁻¹ =
        Complex.exp (Real.pi * Complex.I * (m : ℂ)) := inv_eq_of_mul_eq_one_right hzz
    rw [hinv, sub_self, zero_div]

private lemma abs_sin_pi_ge (η : ℝ) (h0 : η ≠ 0) (h : |η| ≤ 1/2) :
    2 * |η| ≤ |Real.sin (Real.pi * η)| := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have habs : |η| = -η := abs_of_neg hneg
    have hsin : Real.sin (Real.pi * η) = -Real.sin (Real.pi * (-η)) := by
      rw [show Real.pi * η = -(Real.pi * (-η)) by ring, Real.sin_neg]
    rw [habs, hsin, abs_neg]
    have hpos' : (0:ℝ) < -η := by linarith
    have harg0 : (0:ℝ) ≤ Real.pi * (-η) := le_of_lt (mul_pos Real.pi_pos hpos')
    have hle : Real.pi * (-η) ≤ Real.pi / 2 := by
      have h2 : -η ≤ 1/2 := by rw [← habs]; exact h
      nlinarith [Real.pi_pos]
    have hm := Real.mul_le_sin harg0 hle
    have heq : 2 / Real.pi * (Real.pi * (-η)) = 2 * (-η) := by field_simp
    rw [heq] at hm
    have hsp : 0 ≤ Real.sin (Real.pi * (-η)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by nlinarith [Real.pi_pos])
    rw [abs_of_nonneg hsp]
    exact hm
  · have habs : |η| = η := abs_of_pos hpos
    have harg0 : (0:ℝ) ≤ Real.pi * η := le_of_lt (mul_pos Real.pi_pos hpos)
    have hle : Real.pi * η ≤ Real.pi / 2 := by
      have h2 : η ≤ 1/2 := by rw [← habs]; exact h
      nlinarith [Real.pi_pos]
    have hm := Real.mul_le_sin harg0 hle
    have heq : 2 / Real.pi * (Real.pi * η) = 2 * η := by field_simp
    rw [heq] at hm
    have hsp : 0 ≤ Real.sin (Real.pi * η) :=
      Real.sin_nonneg_of_nonneg_of_le_pi harg0 (by nlinarith [Real.pi_pos])
    rw [abs_of_nonneg hsp, habs]
    exact hm

private lemma sum_Icc_eC_geom (η : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, eC (η * (k : ℝ)) = eC η * ∑ j ∈ Finset.range N, (eC η) ^ j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, eC_nat_mul, pow_succ]
    ring

private lemma norm_sum_Icc_eC_le (η : ℝ) (N : ℕ) (hsin : Real.sin (Real.pi * η) ≠ 0) :
    ‖∑ k ∈ Finset.Icc 1 N, eC (η * (k : ℝ))‖ ≤ 1 / |Real.sin (Real.pi * η)| := by
  have hr : eC η ≠ 1 := by
    intro h
    have h0 : ‖1 - eC η‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [norm_one_sub_eC, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · norm_num at h0
    · exact hsin (abs_eq_zero.mp h0)
  rw [sum_Icc_eC_geom, geom_sum_eq hr]
  have hden : ‖eC η - 1‖ = 2 * |Real.sin (Real.pi * η)| := by
    rw [norm_sub_rev]; exact norm_one_sub_eC η
  have hnum : ‖(eC η) ^ N - 1‖ ≤ 2 := by
    have h1 : ‖(eC η) ^ N‖ = 1 := by rw [norm_pow, norm_eC_real, one_pow]
    calc ‖(eC η) ^ N - 1‖ ≤ ‖(eC η) ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
  have hS : (0:ℝ) < |Real.sin (Real.pi * η)| := abs_pos.mpr hsin
  rw [norm_mul, norm_eC_real, one_mul, norm_div, hden]
  rw [show (1:ℝ) / |Real.sin (Real.pi * η)| = 2 / (2 * |Real.sin (Real.pi * η)|) by
    field_simp]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact hnum

private lemma norm_T_le (P X : ℝ) (η : ℝ) (hη : η ≠ 0) (hη2 : |η| ≤ 1/2) :
    ‖T P X η‖ ≤ 1 / |η| := by
  have hsin0 : Real.sin (Real.pi * η) ≠ 0 := by
    intro h
    have h1 := abs_sin_pi_ge η hη hη2
    rw [h, abs_zero] at h1
    have h2 : 0 < |η| := abs_pos.mpr hη
    linarith
  have hSp : 0 < |Real.sin (Real.pi * η)| := abs_pos.mpr hsin0
  have hηpos : (0:ℝ) < |η| := abs_pos.mpr hη
  have hIcc : ∀ N : ℕ, ‖∑ k ∈ Finset.Icc 1 N, eC (η * (k : ℝ))‖ ≤
      1 / |Real.sin (Real.pi * η)| := fun N => norm_sum_Icc_eC_le η N hsin0
  have hT : T P X η = ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ)) := rfl
  have hkey : ‖∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ))‖ ≤ 2 / |Real.sin (Real.pi * η)| := by
    by_cases hMN : ⌊P⌋₊ < ⌊X⌋₊
    · have hunion : Finset.Icc 1 ⌊X⌋₊ = Finset.Icc 1 ⌊P⌋₊ ∪ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊ := by
        ext k
        simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hdisj : Disjoint (Finset.Icc 1 ⌊P⌋₊) (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊) := by
        rw [Finset.disjoint_left]
        intro k h1 h2
        simp only [Finset.mem_Icc] at h1
        simp only [Finset.mem_Ioc] at h2
        omega
      have hsplit : ∑ k ∈ Finset.Icc 1 ⌊X⌋₊, eC (η * (k : ℝ)) =
          (∑ k ∈ Finset.Icc 1 ⌊P⌋₊, eC (η * (k : ℝ))) +
            ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ)) := by
        rw [hunion, Finset.sum_union hdisj]
      have h1 := hIcc ⌊X⌋₊
      rw [hsplit] at h1
      have h2 := hIcc ⌊P⌋₊
      have hsub := norm_sub_le ((∑ k ∈ Finset.Icc 1 ⌊P⌋₊, eC (η * (k : ℝ))) +
          ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ)))
        (∑ k ∈ Finset.Icc 1 ⌊P⌋₊, eC (η * (k : ℝ)))
      have hEq : ((∑ k ∈ Finset.Icc 1 ⌊P⌋₊, eC (η * (k : ℝ))) +
          ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ))) -
          (∑ k ∈ Finset.Icc 1 ⌊P⌋₊, eC (η * (k : ℝ))) =
          ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (k : ℝ)) := by ring
      rw [hEq] at hsub
      have hsum : (1:ℝ) / |Real.sin (Real.pi * η)| + 1 / |Real.sin (Real.pi * η)| =
          2 / |Real.sin (Real.pi * η)| := by ring
      linarith [hsub, h1, h2, hsum]
    · have hemp : Finset.Ioc ⌊P⌋₊ ⌊X⌋₊ = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [hemp, Finset.sum_empty, norm_zero]
      positivity
  rw [hT]
  refine hkey.trans ?_
  have h2t := abs_sin_pi_ge η hη hη2
  calc 2 / |Real.sin (Real.pi * η)| ≤ 2 / (2 * |η|) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) h2t
    _ = 1 / |η| := by field_simp

private lemma integral_inv_sq (A B : ℝ) (h0 : ∀ x ∈ Set.uIcc A B, x ≠ 0) :
    ∫ η in A..B, 1 / η ^ 2 = 1 / A - 1 / B := by
  have hderiv : ∀ x ∈ Set.uIcc A B, HasDerivAt (fun y : ℝ => -(1 / y)) (1 / x ^ 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := h0 x hx
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) ((-1) / x ^ 2) x := (hasDerivAt_id x).inv hx0
    have hneg : HasDerivAt (fun y : ℝ => -(1 / y)) (1 / x ^ 2) x := by
      have h := hinv.const_mul (-1 : ℝ)
      have hfun : (fun y : ℝ => (-1) * y⁻¹) = fun y : ℝ => -(1 / y) := by
        funext y; simp [one_div]
      rw [hfun] at h
      have hval : ((-1:ℝ) * ((-1) / x ^ 2)) = 1 / x ^ 2 := by ring
      rw [hval] at h
      exact h
    exact hneg
  have hint : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : x ≠ 0 := h0 x hx
    have hx2 : x ^ 2 ≠ 0 := by positivity
    have hc : ContinuousAt (fun y : ℝ => (y ^ 2)⁻¹) x :=
      ContinuousAt.inv₀ (continuousAt_id.pow 2) hx2
    have heq : (fun y : ℝ => 1 / y ^ 2) = fun y : ℝ => (y ^ 2)⁻¹ := by
      funext y; simp [one_div]
    rw [heq]
    exact hc.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [one_div]
  ring

private lemma annulus_right_le (P X : ℝ) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2) :
    ∫ η in a..(1/2 : ℝ), ‖T P X η‖ ^ 2 ≤ 1 / a := by
  have hcontT : Continuous fun η : ℝ => T P X η := by
    simp only [T]
    exact continuous_finsetSum _ (fun k _ => by simp only [eC]; fun_prop)
  have hint1 : IntervalIntegrable (fun η : ℝ => ‖T P X η‖ ^ 2) MeasureTheory.volume a (1/2) :=
    (hcontT.norm.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun η : ℝ => 1 / η ^ 2) MeasureTheory.volume a (1/2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : x ≠ 0 := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hx2 : x ^ 2 ≠ 0 := by positivity
    have hc : ContinuousAt (fun y : ℝ => (y ^ 2)⁻¹) x :=
      ContinuousAt.inv₀ (continuousAt_id.pow 2) hx2
    have heq : (fun y : ℝ => 1 / y ^ 2) = fun y : ℝ => (y ^ 2)⁻¹ := by
      funext y; simp [one_div]
    rw [heq]
    exact hc.continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on ha2 hint1 hint2 (fun x hx => ?_)
  · have hval : ∫ x in a..(1/2 : ℝ), 1 / x ^ 2 = 1 / a - 2 := by
      rw [integral_inv_sq a (1/2) (fun x hx => by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)]
      norm_num
    rw [hval] at hmono
    have : (0:ℝ) ≤ 1 / a := by positivity
    linarith
  · have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hxabs : |x| = x := abs_of_pos hx0
    have hb := norm_T_le P X x hx0.ne' (by rw [hxabs]; exact hx.2)
    have h1 : ‖T P X x‖ ^ 2 ≤ (1 / |x|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have h2 : (1 / |x|) ^ 2 = 1 / x ^ 2 := by rw [hxabs]; field_simp
    linarith [h1, h2]

private lemma annulus_left_le (P X : ℝ) (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 1/2) :
    ∫ η in (-1/2 : ℝ)..(-a), ‖T P X η‖ ^ 2 ≤ 1 / a := by
  have hcontT : Continuous fun η : ℝ => T P X η := by
    simp only [T]
    exact continuous_finsetSum _ (fun k _ => by simp only [eC]; fun_prop)
  have hint1 : IntervalIntegrable (fun η : ℝ => ‖T P X η‖ ^ 2) MeasureTheory.volume (-1/2 : ℝ) (-a) :=
    (hcontT.norm.pow 2).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun η : ℝ => 1 / η ^ 2) MeasureTheory.volume (-1/2 : ℝ) (-a) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : x ≠ 0 := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hx2 : x ^ 2 ≠ 0 := by positivity
    have hc : ContinuousAt (fun y : ℝ => (y ^ 2)⁻¹) x :=
      ContinuousAt.inv₀ (continuousAt_id.pow 2) hx2
    have heq : (fun y : ℝ => 1 / y ^ 2) = fun y : ℝ => (y ^ 2)⁻¹ := by
      funext y; simp [one_div]
    rw [heq]
    exact hc.continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on (by linarith : (-1/2 : ℝ) ≤ -a) hint1 hint2
    (fun x hx => ?_)
  · have hval : ∫ x in (-1/2 : ℝ)..(-a), 1 / x ^ 2 = 1 / a - 2 := by
      rw [integral_inv_sq (-1/2 : ℝ) (-a) (fun x hx => by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith)]
      field_simp
      ring
    rw [hval] at hmono
    have : (0:ℝ) ≤ 1 / a := by positivity
    linarith
  · have hxneg : x < 0 := by
      rcases Set.mem_Icc.mp hx with ⟨h1, h2⟩
      linarith
    have hxabs : |x| = -x := abs_of_neg hxneg
    have hle : |x| ≤ 1/2 := by
      rw [hxabs]
      rcases Set.mem_Icc.mp hx with ⟨h1, h2⟩
      linarith
    have hb := norm_T_le P X x hxneg.ne (by rw [hxabs]; linarith [Set.mem_Icc.mp hx |>.2])
    have h1 : ‖T P X x‖ ^ 2 ≤ (1 / |x|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have h2 : (1 / |x|) ^ 2 = 1 / x ^ 2 := by
      rw [hxabs]; field_simp
    linarith [h1, h2]

private lemma continuous_T (P X : ℝ) : Continuous fun η : ℝ => T P X η := by
  simp only [T]
  exact continuous_finsetSum _ (fun k _ => by simp only [eC]; fun_prop)

private lemma continuous_eC_neg_mul (r : ℝ) : Continuous fun η : ℝ => eC (-(η * r)) := by
  simp only [eC]
  fun_prop

private lemma integral_T_sq_mul (P X : ℝ) (n : ℕ) :
    ∫ η in (-1/2:ℝ)..(1/2), T P X η ^ 2 * eC (-(η * (n : ℝ))) =
      (((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)).card : ℂ) := by
  have hcont : ∀ r : ℝ, Continuous fun η : ℝ => eC (η * r) := by
    intro r
    simp only [eC]
    fun_prop
  have hpt : ∫ η in (-1/2:ℝ)..(1/2), T P X η ^ 2 * eC (-(η * (n : ℝ))) =
      ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, ∫ η in (-1/2:ℝ)..(1/2),
        ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) : ℝ)) := by
    have hexp : ∀ η : ℝ, T P X η ^ 2 * eC (-(η * (n : ℝ))) =
        ∑ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
          eC (η * (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) : ℝ)) := by
      intro η
      simp only [T, pow_two]
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [eC_add_real, eC_add_real]
      congr 1
      push_cast
      ring
    simp only [hexp]
    rw [intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)]
    intro k _
    exact (by
      have hc : Continuous fun η : ℝ =>
          ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) : ℝ)) :=
        continuous_finsetSum _ (fun l _ => hcont _)
      exact hc.intervalIntegrable _ _)
  rw [hpt]
  have hstep : ∀ k : ℕ, ∫ η in (-1/2:ℝ)..(1/2),
        ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊, eC (η * (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) : ℝ)) =
      ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
        (if (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) = 0) then (1 : ℂ) else 0) := by
    intro k
    rw [intervalIntegral.integral_finsetSum (μ := MeasureTheory.volume)]
    · exact Finset.sum_congr rfl (fun l _ => integral_eC_int _)
    · intro l _
      exact (hcont _).intervalIntegrable _ _
  refine (Finset.sum_congr rfl (fun k _ => hstep k)).trans ?_
  -- count the pairs
  have hinner : ∀ k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
      ∑ l ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
        (if (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) = 0) then (1 : ℂ) else 0) =
      if n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊ then 1 else 0 := by
    intro k hk
    by_cases hkn : k ≤ n
    · rw [← Finset.sum_ite_eq' (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊) (n - k) (fun _ => (1 : ℂ))]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hiff : ((((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ) = 0)) ↔ (l = n - k) := by omega
      simp only [hiff]
    · have hnk : ¬ (n - k) ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊ := by
        intro h
        have h1 : ⌊P⌋₊ < n - k := (Finset.mem_Ioc.mp h).1
        omega
      rw [if_neg hnk]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      have : (((k : ℤ) + (l : ℤ) - (n : ℤ) : ℤ)) ≠ 0 := by omega
      rw [if_neg this]
  refine (Finset.sum_congr rfl (fun k hk => hinner k hk)).trans ?_
  exact Finset.sum_boole (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊) (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)

private lemma filter_card_bounds (P X : ℝ) (n : ℕ) (hnN : n ≤ ⌊X⌋₊) :
    ((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)).card ≤ n ∧
      n ≤ ((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)).card + (2 * ⌊P⌋₊ + 1) := by
  have hset : (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)
      = Finset.Ioc ⌊P⌋₊ (n - ⌊P⌋₊ - 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [hset, Nat.card_Ioc]
  constructor <;> omega

/-! ### Private helpers for `mv_gallagher_lemma42_step` -/

section

open MeasureTheory

private lemma eC_as_exp (η : ℝ) (n : ℕ) :
    eC (η * (n : ℝ)) = Complex.exp ((2 * Real.pi * η * Complex.I) * (n : ℝ)) := by
  simp only [eC]
  congr 1
  push_cast
  ring

open Classical in
/-- `W(χ,η)` is the exponential sum with the coefficients of `sharpSum`. -/
private lemma Wchi_eq_sum {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (η : ℝ) :
    Wchi P X χ η = ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
      (((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) - (if χ = 1 then (1 : ℂ) else 0)) *
        Complex.exp ((2 * Real.pi * η * Complex.I) * (n : ℝ))) := by
  have hS : Schi P X χ η = ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
      (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) *
        Complex.exp ((2 * Real.pi * η * Complex.I) * (n : ℝ)) := by
    simp only [Schi]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hp : Nat.Prime n <;> simp [hp, eC_as_exp]
  by_cases h1 : χ = 1
  · have hT : T P X η = ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
        Complex.exp ((2 * Real.pi * η * Complex.I) * (n : ℝ)) := by
      simp only [T]
      exact Finset.sum_congr rfl (fun n _ => eC_as_exp η n)
    rw [Wchi, if_pos h1, hS, hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [if_pos h1]
    ring
  · rw [Wchi, if_neg h1, sub_zero, hS]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [if_neg h1]
    ring

open Classical in
/-- The filtered moving window of `sharpSum` coefficients is `sharpSum`, shifted. -/
private lemma filter_sharpSum {r : ℕ} (P X : ℝ) (χ : DirichletCharacter ℂ r) (h' x : ℝ) :
    (∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'),
        ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
          (if χ = 1 then (1 : ℂ) else 0)))
      = sharpSum P X χ (x + h') h' := by
  rw [sharpSum]
  simp only [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hx : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'
  · have hx' : (x + h') - h' < (n : ℝ) ∧ (n : ℝ) ≤ x + h' := by
      rw [add_sub_cancel_right]; exact hx
    rw [if_pos hx, if_pos hx']
  · have hx' : ¬ ((x + h') - h' < (n : ℝ) ∧ (n : ℝ) ≤ x + h') := by
      rw [add_sub_cancel_right]; exact hx
    rw [if_neg hx, if_neg hx']

open Classical in
/-- The mean square of the moving window, from Gallagher's lemma and the `sharpSum` bound. -/
private lemma gallagher_window_bound {r : ℕ} (P X : ℝ) (hX0 : 0 < X) (hP1 : 1 ≤ P)
    (χ : DirichletCharacter ℂ r) (M h' : ℝ) (hM : 0 ≤ M) (hh : 0 < h') (hhX : h' ≤ X)
    (hb : ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
      ‖sharpSum P X χ x h‖ ≤ M * (h + X / P)) :
    ∫ x : ℝ, ‖(∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'),
        ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
          (if χ = 1 then (1 : ℂ) else 0)))‖ ^ 2 ≤ 2 * X * (M * (h' + X / P)) ^ 2 := by
  let Wf : ℝ → ℂ := fun x => ∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
    (Set.Ico ((n : ℝ) - h') (n : ℝ)).indicator
      (fun _ => ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
        (if χ = 1 then (1 : ℂ) else 0))) x
  have hind : ∀ n : ℕ, ∀ x : ℝ,
      (Set.Ico ((n : ℝ) - h') (n : ℝ)).indicator
        (fun _ => ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
          (if χ = 1 then (1 : ℂ) else 0))) x
        = (if x < (n : ℝ) ∧ (n : ℝ) ≤ x + h' then
            ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
              (if χ = 1 then (1 : ℂ) else 0)) else 0) := by
    intro n x
    by_cases hx : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'
    · have hi : x ∈ Set.Ico ((n : ℝ) - h') (n : ℝ) := by
        rw [Set.mem_Ico]; exact ⟨by linarith [hx.1, hx.2], hx.1⟩
      rw [Set.indicator_of_mem hi, if_pos hx]
    · have hi : x ∉ Set.Ico ((n : ℝ) - h') (n : ℝ) := by
        rw [Set.mem_Ico]
        intro hc
        exact hx ⟨hc.2, by linarith [hc.1]⟩
      rw [Set.indicator_of_notMem hi, if_neg hx]
  have hfilter_ne : ∀ x : ℝ, ‖(∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'),
        ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
          (if χ = 1 then (1 : ℂ) else 0)))‖ = ‖Wf x‖ := by
    intro x
    dsimp only [Wf]
    rw [Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact (hind n x).symm
  have hmem : MemLp Wf 2 := by
    dsimp only [Wf]
    apply memLp_finsetSum
    intro n _
    exact memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet _ (Or.inr (by simp))
  have hint : Integrable (fun x => ‖Wf x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hWval : ∀ x : ℝ, Wf x = sharpSum P X χ (x + h') h' := by
    intro x
    rw [← filter_sharpSum (P := P) (X := X) (χ := χ) (h' := h') (x := x)]
    dsimp only [Wf]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact hind n x
  have hzero : ∀ x : ℝ, x ∉ Set.Ioc (-h') (⌊X⌋₊ : ℝ) → Wf x = 0 := by
    intro x hx
    dsimp only [Wf]
    refine Finset.sum_eq_zero (fun n hn => ?_)
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by
      have h2 : 1 ≤ n := by omega
      exact_mod_cast h2
    have hn2' : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hn2
    rw [Set.indicator_of_notMem]
    intro hc
    rw [Set.mem_Ico] at hc
    exact hx (Set.mem_Ioc.mpr ⟨by linarith [hc.1, hn1'], by linarith [hc.2, hn2']⟩)
  have hpoint : ∀ x ∈ Set.Ioc (-h') (⌊X⌋₊ : ℝ),
      ‖Wf x‖ ^ 2 ≤ (M * (h' + X / P)) ^ 2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_Ioc.mp hx
    have hx1' : 0 ≤ x + h' := by linarith
    have hx2' : x + h' ≤ 2 * X := by
      have h2 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
      linarith
    rw [hWval x]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb (x + h') h' hx1' hx2' hh hhX) 2
  have heq : ∫ x : ℝ, ‖Wf x‖ ^ 2 = ∫ x in Set.Ioc (-h') (⌊X⌋₊ : ℝ), ‖Wf x‖ ^ 2 := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Ioc (-h') (⌊X⌋₊ : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero x hx, norm_zero]
      norm_num
  have hstep : ∫ x in Set.Ioc (-h') (⌊X⌋₊ : ℝ), ‖Wf x‖ ^ 2
      ≤ ∫ x in Set.Ioc (-h') (⌊X⌋₊ : ℝ), (M * (h' + X / P)) ^ 2 := by
    apply setIntegral_mono_on hint.integrableOn _ measurableSet_Ioc hpoint
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hval : ∫ x in Set.Ioc (-h') (⌊X⌋₊ : ℝ), (M * (h' + X / P)) ^ 2
      = ((⌊X⌋₊ : ℝ) + h') * (M * (h' + X / P)) ^ 2 := by
    rw [← intervalIntegral.integral_of_le (by linarith : (-h') ≤ (⌊X⌋₊ : ℝ))]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hfin : ((⌊X⌋₊ : ℝ) + h') * (M * (h' + X / P)) ^ 2
      ≤ 2 * X * (M * (h' + X / P)) ^ 2 := by
    have hc : 0 ≤ (M * (h' + X / P)) ^ 2 := by positivity
    have h1 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
    nlinarith
  have hconv : ∫ x : ℝ, ‖(∑ n ∈ (Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
        (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h'),
        ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
          (if χ = 1 then (1 : ℂ) else 0)))‖ ^ 2 = ∫ x : ℝ, ‖Wf x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hfilter_ne x]
  rw [hconv, heq]
  linarith [hstep, hval, hfin]

end

/-! ### The leaves -/

/-- LEAF: P0015 displays (6.1) to (6.9), pages 361 to 363, class HARD.
For `α ∈ 𝔐(q,a)` expand `S(α)` by characters, (6.1) and (6.2); square, (6.3); integrate over the
arcs of modulus `q`, (6.4); bound the second and third terms by Cauchy Schwarz with (6.7)
`∫|T|² ≤ X`, giving (6.6); group by primitive characters and apply Lemma 5.5, giving (6.8):
the remainder is `≪ n φ(n)⁻¹ (W X^{1/2} + W²)` with `W` of (6.9). Constants absolute, P0015 page
354. No zero free hypothesis is used, since `W(χ,η)` is defined without the exceptional term. -/
theorem mv_remainder_66_68 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) -
          ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, mainWeight q n * arcIntegral (X ^ (6 * δ)) X q n‖ ≤
        C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  sorry

/-- LEAF: P0015 displays (6.10) and (6.11), page 363, class MEDIUM.
`T(η) ≪ ‖η‖⁻¹` gives `∫_{1/qQ}^{1/2} |T|² ≪ qQ`, so the arc integral is
`∫_0^1 T(η)² e(-nη) dη + O(qQ) = n + O(qQ)` for `n ≤ X`, with `qQ = qX/P`. -/
theorem mv_arc_main_611 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (6 * δ) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcIntegral (X ^ (6 * δ)) X q n - (n : ℂ)‖ ≤ C * q * (X / X ^ (6 * δ)) := by
  refine ⟨6, by norm_num, ?_⟩
  intro δ hδ hδ1
  refine ⟨16, ?_⟩
  intro X hX q hq hqP n hn hnX
  have hX0 : (0:ℝ) < X := by linarith
  have hX1 : (1:ℝ) ≤ X := by linarith
  have h6d1 : 6 * δ ≤ 1 := by nlinarith
  have hP0 : (0:ℝ) < X ^ (6 * δ) := Real.rpow_pos_of_pos hX0 _
  have hPX : X ^ (6 * δ) ≤ X := by
    calc X ^ (6 * δ) ≤ X ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 h6d1
      _ = X := Real.rpow_one X
  have hP2 : (X ^ (6 * δ)) ^ 2 ≤ X := by
    have hsq : (X ^ (6 * δ)) ^ 2 = X ^ (6 * δ) * X ^ (6 * δ) := by ring
    rw [hsq, ← Real.rpow_add hX0]
    calc X ^ (6 * δ + 6 * δ) ≤ X ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hnN : n ≤ ⌊X⌋₊ := Nat.le_floor hnX
  set P : ℝ := X ^ (6 * δ) with hPdef
  set c : ℕ := ((Finset.Ioc ⌊P⌋₊ ⌊X⌋₊).filter
    (fun k => n - k ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊)).card with hcdef
  set a : ℝ := P / ((q:ℝ) * X) with hadef
  set F : ℝ → ℂ := fun η => T P X η ^ 2 * eC (-(η * (n : ℝ))) with hFdef
  have hP0' : (0:ℝ) < P := by rw [hPdef]; exact hP0
  have hPX' : P ≤ X := by rw [hPdef]; exact hPX
  have hP2' : P ^ 2 ≤ X := by rw [hPdef]; exact hP2
  have ha : 0 < a := by rw [hadef]; positivity
  have hcontF : Continuous F := by
    rw [hFdef]
    exact ((continuous_T P X).pow 2).mul (continuous_eC_neg_mul (n : ℝ))
  -- the exact value of the full-period integral
  have hFval : ∀ η : ℝ, F η = T P X η ^ 2 * eC (-(η * (n : ℝ))) := by
    intro η
    rw [hFdef]
  have hI : ∫ η in (-1/2 : ℝ)..(1/2), F η = (c : ℂ) := by
    have h := integral_T_sq_mul P X n
    rw [← hcdef] at h
    rw [← h]
  -- the combinatorial bound
  obtain ⟨hb1, hb2⟩ := filter_card_bounds P X n hnN
  rw [← hcdef] at hb1 hb2
  have hB : ‖(∫ η in (-1/2 : ℝ)..(1/2), F η) - (n : ℂ)‖ ≤ 2 * (⌊P⌋₊ : ℝ) + 1 := by
    rw [hI]
    have hc1 : (c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hb1
    have hc2 : (n : ℝ) ≤ (c : ℝ) + (2 * (⌊P⌋₊ : ℝ) + 1) := by exact_mod_cast hb2
    have hcast : ((c : ℕ) : ℂ) - (n : ℂ) = (((c : ℝ) - (n : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- the two annulus pieces
  have h2PX : 2 * P ≤ X := by
    have h4 : 4 * P ^ 2 ≤ X ^ 2 := by nlinarith
    have hfac : X ^ 2 - 4 * P ^ 2 = (X - 2 * P) * (X + 2 * P) := by ring
    have hpos : 0 < X + 2 * P := by positivity
    have hnn : 0 ≤ (X - 2 * P) * (X + 2 * P) := by rw [← hfac]; linarith
    have hle : 0 ≤ X - 2 * P := by
      by_contra hc
      push_neg at hc
      nlinarith [hnn, hpos, hc]
    linarith
  have ha2 : a ≤ 1/2 := by
    rw [hadef, div_le_iff₀ (by positivity)]
    nlinarith [h2PX, hq1, hP0', hX0]
  have hA : ‖∫ η in (-1/2 : ℝ)..(-a), F η‖ ≤ 1 / a := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith : (-1/2 : ℝ) ≤ -a)).trans ?_
    have heq : ∫ η in (-1/2 : ℝ)..(-a), ‖F η‖ =
        ∫ η in (-1/2 : ℝ)..(-a), ‖T P X η‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro η _
      rw [hFdef]
      simp only [norm_mul, norm_pow, norm_eC_real]
      ring
    rw [heq]
    exact annulus_left_le P X a ha ha2
  have hC : ‖∫ η in a..(1/2 : ℝ), F η‖ ≤ 1 / a := by
    refine (intervalIntegral.norm_integral_le_integral_norm ha2).trans ?_
    have heq : ∫ η in a..(1/2 : ℝ), ‖F η‖ = ∫ η in a..(1/2 : ℝ), ‖T P X η‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro η _
      rw [hFdef]
      simp only [norm_mul, norm_pow, norm_eC_real]
      ring
    rw [heq]
    exact annulus_right_le P X a ha ha2
  -- split the full period
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (f := F) (a := (-1/2 : ℝ)) (b := -a) (c := a)
    (hcontF.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hcontF.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (f := F) (a := (-1/2 : ℝ)) (b := a) (c := (1/2 : ℝ))
    (hcontF.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hcontF.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have hdec : ∫ η in (-a)..a, F η = (∫ η in (-1/2 : ℝ)..(1/2), F η) -
      (∫ η in (-1/2 : ℝ)..(-a), F η) - (∫ η in a..(1/2 : ℝ), F η) := by
    rw [← hsplit2, ← hsplit1]
    ring
  -- the triangle inequality
  have htri : ‖(∫ η in (-1/2 : ℝ)..(1/2), F η) - (∫ η in (-1/2 : ℝ)..(-a), F η) -
      (∫ η in a..(1/2 : ℝ), F η) - (n : ℂ)‖ ≤
      ‖(∫ η in (-1/2 : ℝ)..(1/2), F η) - (n : ℂ)‖ + ‖∫ η in (-1/2 : ℝ)..(-a), F η‖ +
        ‖∫ η in a..(1/2 : ℝ), F η‖ := by
    have e1 : (∫ η in (-1/2 : ℝ)..(1/2), F η) - (∫ η in (-1/2 : ℝ)..(-a), F η) -
        (∫ η in a..(1/2 : ℝ), F η) - (n : ℂ) =
        ((∫ η in (-1/2 : ℝ)..(1/2), F η) - (n : ℂ)) - (∫ η in (-1/2 : ℝ)..(-a), F η) -
          (∫ η in a..(1/2 : ℝ), F η) := by ring
    rw [e1]
    have hstep1 := norm_sub_le (((∫ η in (-1/2 : ℝ)..(1/2), F η) - (n : ℂ)) -
      (∫ η in (-1/2 : ℝ)..(-a), F η)) (∫ η in a..(1/2 : ℝ), F η)
    have hstep2 := norm_sub_le ((∫ η in (-1/2 : ℝ)..(1/2), F η) - (n : ℂ))
      (∫ η in (-1/2 : ℝ)..(-a), F η)
    linarith
  have hbound : ‖(∫ η in (-a)..a, F η) - (n : ℂ)‖ ≤
      2 * (⌊P⌋₊ : ℝ) + 1 + 1 / a + 1 / a := by
    rw [hdec]
    linarith [htri, hB, hA, hC]
  -- final arithmetic
  have h1a : 1 / a = (q:ℝ) * (X / P) := by
    rw [hadef]
    field_simp
  have key : 2 * (⌊P⌋₊ : ℝ) + 1 ≤ 4 * ((q:ℝ) * (X / P)) := by
    have hM : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP0'.le
    have hnum : (2 * (⌊P⌋₊ : ℝ) + 1) * P ≤ 4 * (q:ℝ) * X := by
      nlinarith [hP2', hPX', hq1, hP0', hM]
    calc 2 * (⌊P⌋₊ : ℝ) + 1 ≤ (4 * (q:ℝ) * X) / P := by
          rw [le_div_iff₀ hP0']
          linarith
      _ = 4 * ((q:ℝ) * (X / P)) := by field_simp
  have hgoal : 2 * (⌊P⌋₊ : ℝ) + 1 + 1 / a + 1 / a =
      (2 * (⌊P⌋₊ : ℝ) + 1) + 2 * ((q:ℝ) * (X / P)) := by
    rw [h1a]
    ring
  have harc : arcIntegral P X q n = ∫ η in (-a)..a, F η := by
    simp only [arcIntegral]
    rw [hFdef, hadef]
  rw [harc]
  calc ‖(∫ η in (-a)..a, F η) - (n : ℂ)‖ ≤ 2 * (⌊P⌋₊ : ℝ) + 1 + 1 / a + 1 / a := hbound
    _ = (2 * (⌊P⌋₊ : ℝ) + 1) + 2 * ((q:ℝ) * (X / P)) := hgoal
    _ ≤ 6 * (q:ℝ) * (X / P) := by linarith [key]

/-- LEAF: P0015 display (6.13), page 363, class MEDIUM.
By (5.2), `Q Σ_{q≤P} μ(q)² φ(q)⁻² |c_q(n)| q ≪ Q n φ(n)⁻¹ d(n) log P ≪ X^{1+δ} P⁻¹`, with
`Q = X/P`; the `X^δ` absorbs `d(n) log P` and needs `X` large in terms of `δ`. -/
theorem mv_truncation_613 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (X / X ^ (6 * δ)) * ∑ q ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊, ‖mainWeight q n‖ * q ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  sorry

/-- LEAF: P0015 display (6.16), page 363, class MEDIUM.
`𝔖(n) = Σ_{q≥1} μ(q)² φ(q)⁻² c_q(-n) = ∏_{p∤n} (1 - (p-1)⁻²) ∏_{p∣n} (1 + (p-1)⁻¹)`, by (5.2);
the series converges absolutely. The `q = 0` term is zero since `μ(0) = 0`. -/
theorem mv_singular_series_616 (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q : ℕ => ‖mainWeight q n‖) ∧
      HasSum (fun q : ℕ => mainWeight q n) ((singularSeries n : ℝ) : ℂ) := by
  sorry

/-- LEAF: P0015 display (6.14), page 363, class MEDIUM.
Extending the main term to all `q ≥ 1` costs
`n Σ_{q>P} φ(q)⁻¹ φ(q/(q,n))⁻¹ ≪ n P⁻¹ d(n) n φ(n)⁻¹ ≪ X^{1+δ} P⁻¹` for `n ≤ X`. -/
theorem mv_tail_614 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      (n : ℝ) * ∑' q : ℕ, (if X ^ (6 * δ) < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) := by
  sorry

/-- LEAF: P0015 page 366, the first display of section 7, from Lemma 4.2 (Gallagher's Lemma 1),
class MEDIUM. With `κ = 1/(rQ)`,
`W(χ) ≪ X^{1/2} max_{x≤2X} max_{0<h≤X} (h + X P⁻¹)⁻¹ |Σ^#_{x-h<p≤x} χ(p) log p|`.
Stated with any bound `M` for the double maximum; the constant is absolute. -/
theorem mv_gallagher_lemma42_step : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ X ^ (6 * δ) →
      ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → ∀ M : ℝ,
        (∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
          ‖sharpSum (X ^ (6 * δ)) X χ x h‖ ≤ M * (h + X / X ^ (6 * δ))) →
        Wnorm (X ^ (6 * δ)) X χ ≤ C * Real.sqrt X * M := by
  refine ⟨10, by norm_num, ?_⟩
  intro δ hδ hδ1
  refine ⟨1, ?_⟩
  classical
  intro X hX r hr hrP χ hχ M hb
  have hX0 : (0:ℝ) < X := by linarith
  have hX1 : (1:ℝ) ≤ X := by linarith
  set P : ℝ := X ^ (6 * δ) with hPdef
  have hP0 : 0 < P := by rw [hPdef]; exact Real.rpow_pos_of_pos hX0 _
  have hP1 : 1 ≤ P := by rw [hPdef]; exact Real.one_le_rpow hX1 (by linarith)
  have hrP' : (r:ℝ) ≤ P := by rw [hPdef]; exact hrP
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  set κ : ℝ := P / ((r:ℝ) * X) with hκdef
  have hκ : 0 < κ := by rw [hκdef]; positivity
  set h' : ℝ := 1 / (2 * κ) with hhdef
  have hh : 0 < h' := by rw [hhdef]; positivity
  have hhval : h' = (r:ℝ) * X / (2 * P) := by
    rw [hhdef, hκdef]
    field_simp
  have hhX : h' ≤ X := by
    rw [hhval, div_le_iff₀ (by positivity)]
    nlinarith [hrP', hP1, hX0]
  have hM : 0 ≤ M := by
    have h1 := hb 0 h' le_rfl (by positivity) hh hhX
    have h2 : 0 < h' + X / P := by positivity
    by_contra hneg
    push_neg at hneg
    nlinarith [h1, h2, hneg, norm_nonneg (sharpSum P X χ 0 h')]
  have hInt : ∫ η in (-κ)..κ, ‖Wchi P X χ η‖ ^ 2 =
      ∫ t in (-κ)..κ, ‖∑ n ∈ Finset.Ioc ⌊P⌋₊ ⌊X⌋₊,
          (((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
            (if χ = 1 then (1 : ℂ) else 0)) *
            Complex.exp ((2 * Real.pi * t * Complex.I) * (n : ℝ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Wchi_eq_sum P X χ t]
  have hgal := LeanLab.ExceptionalSet.WeightedGallagher264.real_frequency_gallagher
    (s := Finset.Ioc ⌊P⌋₊ ⌊X⌋₊) (ν := fun n : ℕ => (n : ℝ))
    (a := fun n : ℕ => ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) -
      (if χ = 1 then (1 : ℂ) else 0))) hκ
  rw [← hhdef] at hgal
  have hbound := gallagher_window_bound P X hX0 hP1 χ M h' hM hh hhX hb
  have hchain : ∫ η in (-κ)..κ, ‖Wchi P X χ η‖ ^ 2
      ≤ Real.pi ^ 2 * κ ^ 2 * (2 * X * (M * (h' + X / P)) ^ 2) := by
    rw [hInt]
    exact hgal.trans (by
      have h0 : (0:ℝ) ≤ Real.pi ^ 2 * κ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hbound h0)
  have hWnorm : Wnorm P X χ = Real.sqrt (∫ η in (-κ)..κ, ‖Wchi P X χ η‖ ^ 2) := by
    rw [Wnorm]
  rw [hWnorm, Real.sqrt_le_left (by positivity)]
  have hkap : κ * (h' + X / P) ≤ 3 / 2 := by
    rw [hκdef, hhval]
    have hPr : P ≠ 0 := hP0.ne'
    have hXr : X ≠ 0 := hX0.ne'
    have hrne : (r:ℝ) ≠ 0 := hr0.ne'
    rw [show P / ((r:ℝ) * X) * ((r:ℝ) * X / (2 * P) + X / P) = 1 / 2 + 1 / (r:ℝ) by
      field_simp]
    have : 1 / (r:ℝ) ≤ 1 := by
      rw [div_le_one hr0]
      exact hr1
    linarith
  have hkey : Real.pi ^ 2 * κ ^ 2 * (2 * X * (M * (h' + X / P)) ^ 2)
      ≤ (10 * Real.sqrt X * M) ^ 2 := by
    have hXsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0.le
    have hkx : (κ * (h' + X / P)) ^ 2 ≤ 9 / 4 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ κ * (h' + X / P)) hkap 2
      norm_num at h ⊢
      exact h
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_gt_three, Real.pi_lt_four]
    have hfsq : κ ^ 2 * (M * (h' + X / P)) ^ 2 = M ^ 2 * (κ * (h' + X / P)) ^ 2 := by ring
    have hprod : Real.pi ^ 2 * (M ^ 2 * (κ * (h' + X / P)) ^ 2) ≤ 16 * (M ^ 2 * (9 / 4)) := by
      have h3 : Real.pi ^ 2 * (κ * (h' + X / P)) ^ 2 ≤ 16 * (9 / 4) :=
        mul_le_mul hpi2 hkx (by positivity) (by positivity)
      calc Real.pi ^ 2 * (M ^ 2 * (κ * (h' + X / P)) ^ 2)
          = M ^ 2 * (Real.pi ^ 2 * (κ * (h' + X / P)) ^ 2) := by ring
        _ ≤ M ^ 2 * (16 * (9 / 4)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg M)
        _ = 16 * (M ^ 2 * (9 / 4)) := by ring
    have hrhs : (10 * Real.sqrt X * M) ^ 2 = 100 * X * M ^ 2 := by
      rw [mul_pow, mul_pow, hXsq]
      ring
    have hlhs : Real.pi ^ 2 * κ ^ 2 * (2 * X * (M * (h' + X / P)) ^ 2)
        = 2 * X * (Real.pi ^ 2 * (M ^ 2 * (κ * (h' + X / P)) ^ 2)) := by ring
    rw [hrhs, hlhs]
    nlinarith [hprod, hX0, sq_nonneg M]
  calc ∫ η in (-κ)..κ, ‖Wchi P X χ η‖ ^ 2
      ≤ Real.pi ^ 2 * κ ^ 2 * (2 * X * (M * (h' + X / P)) ^ 2) := hchain
    _ ≤ (10 * Real.sqrt X * M) ^ 2 := hkey

/-- LEAF: P0015 Lemma 4.3, pages 357 and 358, Gallagher 1970 Theorem 7 made effective, applied
with `N = 2X`, class HARD, a citation wall. For each zero free constant `a > 0` there are
`c₃ > 0`, `B > 0` and a range `P ≤ N^{c₄}`, here `δ < δ₁`, such that when no primitive character
of modulus at most `P` has a real zero in `[1 - a/log P, 1)`,
`Σ_{q≤P} Σ*_χ max_{x≤N} max_{h≤N} (h + N/P)⁻¹ |Σ^#| ≪ exp(-c₃ log N / log P)`.
Stated with bounds `M r χ` for the maxima. The constants depend on `a`, because MV's absolute
constants come from the zero free constant `c₁` of Lemma 4.1, which here is `min a c` with `c` the
classical constant for complex zeros, Davenport chapter 14. -/
theorem mv_gallagher_lemma43 : ∀ a : ℝ, 0 < a → ∃ c₃ B δ₁ : ℝ, 0 < c₃ ∧ 0 < B ∧ 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      ∃ M : (r : ℕ) → DirichletCharacter ℂ r → ℝ,
        (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ X ^ (6 * δ) → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
          ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
            ‖sharpSum (X ^ (6 * δ)) X χ x h‖ ≤ M r χ * (h + X / X ^ (6 * δ))) ∧
        ∑ r ∈ Icc 1 ⌊X ^ (6 * δ)⌋₊,
            ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 ≤
          B * Real.exp (-(c₃ * Real.log X / Real.log (X ^ (6 * δ)))) := by
  sorry

/-! ### Assembly from the leaves -/

lemma mainWeight_zero (n : ℕ) : mainWeight 0 n = 0 := by
  simp [mainWeight]

/-- The tail of an absolutely summable series beyond a finite set. PROVED. -/
lemma norm_sum_sub_tsum_le {f : ℕ → ℂ} {S : ℂ} (hs : Summable (fun q => ‖f q‖))
    (hS : HasSum f S) (s : Finset ℕ) :
    ‖(∑ q ∈ s, f q) - S‖ ≤ ∑' q : ℕ, (if q ∈ s then 0 else ‖f q‖) := by
  have hf : Summable f := hs.of_norm
  have h1 : (∑ q ∈ s, f q) - S = -∑' q : ℕ, (if q ∈ s then 0 else f q) := by
    have hsplit : ∑' q : ℕ, f q = ∑ q ∈ s, f q + ∑' q : ℕ, (if q ∈ s then 0 else f q) := by
      rw [← hf.sum_add_tsum_compl (s := s), tsum_subtype (↑s : Set ℕ)ᶜ f]
      congr 1
      refine tsum_congr (fun q => ?_)
      by_cases hq : q ∈ s <;> simp [hq, Set.indicator]
    rw [hS.tsum_eq] at hsplit
    rw [hsplit]; ring
  rw [h1, norm_neg]
  have hsum : Summable (fun q : ℕ => (if q ∈ s then 0 else ‖f q‖)) :=
    hs.of_nonneg_of_le (fun q => by split_ifs <;> simp) (fun q => by split_ifs <;> simp)
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr (fun q => ?_)))
  · refine hsum.congr (fun q => ?_)
    by_cases hq : q ∈ s <;> simp [hq]
  · by_cases hq : q ∈ s <;> simp [hq]

/-- P0015 display (6.17): `R₁(n) = 𝔖(n) n + O(X^{1+δ} P⁻¹) + O(n φ(n)⁻¹ (W X^{1/2} + W²))` for
`1 ≤ n ≤ X`. PROVED from the five leaves of section 6. -/
theorem mv_617 : ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
      ‖R1 (X ^ (6 * δ)) X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ)‖ ≤
        C * (X ^ (1 + δ) / X ^ (6 * δ)) + C * ((n : ℝ) / (n.totient : ℝ)) *
          (mvW (X ^ (6 * δ)) X * Real.sqrt X + mvW (X ^ (6 * δ)) X ^ 2) := by
  obtain ⟨C1, hC1, h1⟩ := mv_remainder_66_68
  obtain ⟨C2, hC2, h2⟩ := mv_arc_main_611
  obtain ⟨C3, hC3, h3⟩ := mv_truncation_613
  obtain ⟨C4, hC4, h4⟩ := mv_tail_614
  refine ⟨C1 + C2 * C3 + C4, by positivity, ?_⟩
  intro δ hδ hδ1
  obtain ⟨X1, hX1⟩ := h1 δ hδ hδ1
  obtain ⟨X2, hX2⟩ := h2 δ hδ hδ1
  obtain ⟨X3, hX3⟩ := h3 δ hδ hδ1
  obtain ⟨X4, hX4⟩ := h4 δ hδ hδ1
  refine ⟨max (max X1 X2) (max X3 (max X4 1)), ?_⟩
  intro X hX n hn hnX
  have hXa : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXd : X4 ≤ X := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  have hX1' : (1 : ℝ) ≤ X := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith) _
  set s := Icc 1 ⌊P⌋₊ with hs
  set W := mvW P X
  set ρ := (n : ℝ) / (n.totient : ℝ)
  have hφ : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le n
  have hW0 : 0 ≤ W := by
    refine sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set E := X ^ (1 + δ) / P
  have hE0 : 0 ≤ E := div_nonneg (Real.rpow_nonneg (by linarith) _) hP0
  -- the three pieces
  have hA := hX1 X hXa n hn hnX
  have hB : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ ≤ C2 * C3 * E := by
    calc ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖
        ≤ ∑ q ∈ s, ‖mainWeight q n‖ * (C2 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
          have hqP : (q : ℝ) ≤ P := by
            have := (mem_Icc.mp hq).2
            exact le_trans (by exact_mod_cast this) (Nat.floor_le hP0)
          exact mul_le_mul_of_nonneg_left (hX2 X hXb q hq1 hqP n hn hnX) (norm_nonneg _)
      _ = C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
      _ ≤ C2 * (C3 * E) := mul_le_mul_of_nonneg_left (hX3 X hXc n hn hnX) hC2.le
      _ = C2 * C3 * E := by ring
  have hC : ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤ C4 * E := by
    obtain ⟨hsum, hhas⟩ := mv_singular_series_616 n hn
    have ht := norm_sum_sub_tsum_le hsum hhas s
    have hcongr : ∑' q : ℕ, (if q ∈ s then 0 else ‖mainWeight q n‖) =
        ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
      refine tsum_congr (fun q => ?_)
      by_cases hq0 : q = 0
      · subst hq0; simp [mainWeight_zero]
      · have hiff : q ∈ s ↔ ¬ P < (q : ℝ) := by
          rw [hs, mem_Icc, not_lt]
          constructor
          · rintro ⟨_, h⟩; exact le_trans (by exact_mod_cast h) (Nat.floor_le hP0)
          · intro h; exact ⟨by omega, Nat.le_floor h⟩
        by_cases hq : q ∈ s
        · simp [hq, hiff.mp hq]
        · have : P < (q : ℝ) := by by_contra h; exact hq (hiff.mpr h)
          simp [hq, this]
    rw [hcongr] at ht
    rw [norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖(∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)‖
        ≤ (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ C4 * E := hX4 X hXd n hn hnX
  -- assemble
  have hsplit : R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) =
      (R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n) +
        ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) +
        (n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    push_cast
    have : ∑ q ∈ s, mainWeight q n * (n : ℂ) = ∑ q ∈ s, (n : ℂ) * mainWeight q n :=
      sum_congr rfl (fun q _ => mul_comm _ _)
    rw [this]; ring
  rw [hsplit]
  have hrem : 0 ≤ ρ * (W * Real.sqrt X + W ^ 2) := by positivity
  calc _ ≤ ‖R1 P X (n : ℤ) - ∑ q ∈ s, mainWeight q n * arcIntegral P X q n‖ +
          ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ +
          ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ :=
        norm_add₃_le
    _ ≤ C1 * ρ * (W * Real.sqrt X + W ^ 2) + C2 * C3 * E + C4 * E := by
        gcongr
    _ ≤ (C1 + C2 * C3 + C4) * E + (C1 + C2 * C3 + C4) * ρ * (W * Real.sqrt X + W ^ 2) := by
        have h23 : 0 ≤ C2 * C3 := by positivity
        nlinarith [mul_nonneg h23 hrem, mul_nonneg hC4.le hrem, mul_nonneg hC1.le hE0]

/-- P0015 display (7.1): `W ≪ X^{1/2} exp(-c₆ log X / log P)` when there is no exceptional term,
here for the zero free constant `a`. PROVED from the two leaves of section 7. -/
theorem mv_71 : ∀ a : ℝ, 0 < a → ∃ c₆ B δ₁ : ℝ, 0 < c₆ ∧ 0 < B ∧ 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      mvW (X ^ (6 * δ)) X ≤
        B * Real.sqrt X * Real.exp (-(c₆ * Real.log X / Real.log (X ^ (6 * δ)))) := by
  intro a ha
  obtain ⟨C, hC, hG⟩ := mv_gallagher_lemma42_step
  obtain ⟨c₃, B, δ₁, hc₃, hB, hδ₁, hL⟩ := mv_gallagher_lemma43 a ha
  refine ⟨c₃, C * B, min δ₁ (1 / 100), hc₃, by positivity, lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨X1, hX1⟩ := hG δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨X2, hX2⟩ := hL δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max X1 (max X2 0), ?_⟩
  intro X hX hno
  have hXa : X1 ≤ X := le_trans (le_max_left _ _) hX
  have hXb : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX0 : 0 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨M, hM, hsum⟩ := hX2 X hXb hno
  set P := X ^ (6 * δ) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX0 _
  have hstep : ∀ r ∈ Icc 1 ⌊P⌋₊,
      ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, Wnorm P X χ.1 ≤
        C * Real.sqrt X * ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by
    intro r hr
    have hr1 : 1 ≤ r := (mem_Icc.mp hr).1
    have hrP : (r : ℝ) ≤ P := le_trans (by exact_mod_cast (mem_Icc.mp hr).2) (Nat.floor_le hP0)
    have : NeZero r := ⟨by omega⟩
    rw [mul_finsum]
    refine finsum_le_finsum (Set.toFinite _) (Set.toFinite _) (fun χ => ?_)
    exact hX1 X hXa r hr1 hrP χ.1 χ.2 (M r χ.1) (hM r hr1 hrP χ.1 χ.2)
  calc mvW P X ≤ ∑ r ∈ Icc 1 ⌊P⌋₊, C * Real.sqrt X *
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := sum_le_sum hstep
    _ = C * Real.sqrt X * ∑ r ∈ Icc 1 ⌊P⌋₊,
          ∑ᶠ χ : {χ : DirichletCharacter ℂ r // χ.IsPrimitive}, M r χ.1 := by rw [mul_sum]
    _ ≤ C * Real.sqrt X * (B * Real.exp (-(c₃ * Real.log X / Real.log P))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * B * Real.sqrt X * Real.exp (-(c₃ * Real.log X / Real.log P)) := by ring

/-! ### The faithful twin of `Lemma2NoExcBP` and its assembly -/

/-- P0082 page 358 Lemma 2 for small `δ`, the range Montgomery and Vaughan cover: for every zero
free constant `a > 0` there are `c₁, K > 0` and `δ₁ > 0` such that for `0 < δ < δ₁`,
`P = X^{6δ}`, all large `X` with no exceptional character, and every `1 ≤ m ≤ X`,
`|R₁(m) - m 𝔖(m)| ≤ K m φ(m)⁻¹ X exp(-c₁ log X / log P)`. It differs from `Lemma2NoExcBP` only by
`δ < δ₁` in place of `δ < 1/100`; `lemma2NoExcSmallDelta_of_BP` shows it is weaker. -/
def Lemma2NoExcSmallDelta : Prop :=
  ∀ a : ℝ, 0 < a → ∃ c₁ K : ℝ, 0 < c₁ ∧ 0 < K ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      NoExceptionalReal a (X ^ (6 * δ)) →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ X →
        ‖R1 (X ^ (6 * δ)) X (m : ℤ) - (((m : ℝ) * singularSeries m : ℝ) : ℂ)‖ ≤
          K * ((m : ℝ) / (m.totient : ℝ)) * X *
            Real.exp (-(c₁ * Real.log X / Real.log (X ^ (6 * δ))))

/-- `Lemma2NoExcBP` implies its small `δ` twin. PROVED, sorry free. -/
theorem lemma2NoExcSmallDelta_of_BP (h : Lemma2NoExcBP) : Lemma2NoExcSmallDelta := by
  intro a ha
  obtain ⟨c₁, K, hc₁, hK, hL⟩ := h a ha
  exact ⟨c₁, K, hc₁, hK, 1 / 100, by norm_num, hL⟩

/-- P0082 Lemma 2 for small `δ`, "Combine (6.17) and (7.1) of Montgomery & Vaughan".
PROVED from the seven leaves above: `X^{1+δ}P⁻¹ = X·X^{-5δ}` is below `X exp(-c₆/(6δ))` once
`log X ≥ c₆/(30δ²)`, and `W² ≤ B² X exp(-2c₆ log X / log P)`. -/
theorem lemma2NoExcSmallDelta_of_leaves : Lemma2NoExcSmallDelta := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617
  obtain ⟨c₆, B, δ₁, hc₆, hB, hδ₁, hW⟩ := mv_71 a ha
  refine ⟨c₆, CA * (1 + B + B ^ 2), hc₆, by positivity, min δ₁ (1 / 100),
    lt_min hδ₁ (by norm_num), ?_⟩
  intro δ hδ hδm
  obtain ⟨XA, hXA⟩ := hA δ hδ (lt_of_lt_of_le hδm (min_le_right _ _))
  obtain ⟨XB, hXB⟩ := hW δ hδ (lt_of_lt_of_le hδm (min_le_left _ _))
  refine ⟨max (max XA XB) (max 2 (Real.exp (c₆ / (30 * δ ^ 2)))), ?_⟩
  intro X hX hno m hm hmX
  have hXa : XA ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : (2 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp (c₆ / (30 * δ ^ 2)) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₆ * Real.log X / Real.log (X ^ (6 * δ)) = c₆ / (6 * δ) := by
    rw [hlogP]; field_simp
  have hbA := hXA X hXa m hm hmX
  have hbW := hXB X hXb hno
  rw [hratio] at hbW ⊢
  set e := Real.exp (-(c₆ / (6 * δ))) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; have : 0 < c₆ / (6 * δ) := by positivity
    linarith
  set W := mvW (X ^ (6 * δ)) X
  have hW0 : 0 ≤ W := sum_nonneg (fun r _ => finsum_nonneg (fun χ => Real.sqrt_nonneg _))
  set ρ := (m : ℝ) / (m.totient : ℝ)
  have hφ : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le m
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  -- the first error term
  have hE : X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0, ← Real.exp_sub, he]
    have hsplit : Real.log X * (1 + δ) - Real.log X * (6 * δ) =
        Real.log X + -(5 * δ * Real.log X) := by ring
    rw [hsplit, Real.exp_add, Real.exp_log hX0]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hX0.le
    have hl : c₆ / (30 * δ ^ 2) ≤ Real.log X := by
      rw [← Real.log_exp (c₆ / (30 * δ ^ 2))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h30 : c₆ / (6 * δ) = 5 * δ * (c₆ / (30 * δ ^ 2)) := by field_simp; ring
    rw [h30]
    have : 5 * δ * (c₆ / (30 * δ ^ 2)) ≤ 5 * δ * Real.log X :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    linarith
  -- the W terms
  have hW1 : W * Real.sqrt X ≤ B * X * e := by
    calc W * Real.sqrt X ≤ B * Real.sqrt X * e * Real.sqrt X :=
          mul_le_mul_of_nonneg_right hbW hsq0
      _ = B * X * e := by linear_combination (B * e) * hsq
  have hW2 : W ^ 2 ≤ B ^ 2 * X * e := by
    have h1 : W ^ 2 ≤ (B * Real.sqrt X * e) ^ 2 := pow_le_pow_left₀ hW0 hbW 2
    have h2 : (B * Real.sqrt X * e) ^ 2 = B ^ 2 * X * (e * e) := by
      linear_combination (B ^ 2 * e ^ 2) * hsq
    have h3 : B ^ 2 * X * (e * e) ≤ B ^ 2 * X * e := by
      have : e * e ≤ e := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  calc _ ≤ CA * (X ^ (1 + δ) / X ^ (6 * δ)) + CA * ρ * (W * Real.sqrt X + W ^ 2) := hbA
    _ ≤ CA * (ρ * (X * e)) + CA * ρ * (B * X * e + B ^ 2 * X * e) := by
        have hXe0 : 0 ≤ X * e := by positivity
        gcongr
        calc X ^ (1 + δ) / X ^ (6 * δ) ≤ X * e := hE
          _ ≤ ρ * (X * e) := by nlinarith
    _ = CA * (1 + B + B ^ 2) * ρ * X * e := by ring

/-- P0082 page 362 Lemma 7 case i, the exact statement of `Decomp559b.leaf_absent_selected`,
CONDITIONAL ON `Lemma2NoExcSmallDelta` and `SingularSeriesEvenLowerBP`, the latter proved as
`Prep1121SingSeries.singularSeriesEvenLowerBP_split`. The proof is that of
`DQLeafAbsentSelected.leaf_absent_selected_of_lemma2` with `δ₀` also below `δ₁`. Sorry free. -/
theorem leaf_absent_selected_of_small (hL : Lemma2NoExcSmallDelta)
    (hS : SingularSeriesEvenLowerBP)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              r = 1 →
                c * F γ N ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨c₁, K, hc₁, hK, δ₁, hδ₁, hL⟩ := hL a ha
  obtain ⟨Cs, hCs, hS⟩ := hS
  refine ⟨min δ₁ (c₁ * Cs / (24 * K)), lt_min hδ₁ (by positivity), ?_⟩
  intro δ hδ hδ₀
  have hδ1 : δ < δ₁ := lt_of_lt_of_le hδ₀ (min_le_left _ _)
  have hδ2 : δ < c₁ * Cs / (24 * K) := lt_of_lt_of_le hδ₀ (min_le_right _ _)
  obtain ⟨X₀, hX₀⟩ := hL δ hδ hδ1
  refine ⟨1, one_pos, ?_⟩
  intro κ _ _
  refine ⟨Cs / 4, 1, by positivity, one_pos, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hF.eventually_ge_atTop (max X₀ 2))
  refine ⟨N₀, ?_⟩
  intro N hN r _ _ hs j hj n hn heven hm hr1
  subst hr1
  have hXbig := hN₀ N hN
  have hX₀X : X₀ ≤ F γ N := le_trans (le_max_left _ _) hXbig
  have hX2 : 2 ≤ F γ N := le_trans (le_max_right _ _) hXbig
  have hnoexc := noExceptionalReal_of_selected_one hs
  have hwin := (Finset.mem_filter.mp hn).2
  have hνpos : (0 : ℤ) < nu γ n := by
    have : (0 : ℝ) < (nu γ n : ℝ) := by linarith [hwin.1]
    exact_mod_cast this
  have hj0 : 0 ≤ j := by rcases hj with h | h <;> omega
  have hnn : 0 ≤ nu γ n + j := by omega
  set k : ℕ := (nu γ n + j).toNat with hkdef
  have hk : ((k : ℕ) : ℤ) = nu γ n + j := Int.toNat_of_nonneg hnn
  rw [← hk] at heven hm ⊢
  have hk1 : 1 ≤ k := by omega
  have hkX : (k : ℝ) ≤ F γ N := by exact_mod_cast hm
  have hkeven : Even k := Int.even_coe_nat k |>.mp heven
  have hkhalf : F γ N / 2 < (k : ℝ) := by
    have h1' : (nu γ n : ℤ) ≤ (k : ℤ) := by omega
    have h2' : ((nu γ n : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h1'
    have h3' : ((k : ℤ) : ℝ) = (k : ℝ) := by push_cast; rfl
    linarith [hwin.1]
  have hbound := hX₀ (F γ N) hX₀X hnoexc k hk1 hkX
  set X := F γ N with hXdef
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogP : Real.log (X ^ (6 * δ)) = 6 * δ * Real.log X := Real.log_rpow hX0 _
  have hratio : c₁ * Real.log X / Real.log (X ^ (6 * δ)) = c₁ / (6 * δ) := by
    rw [hlogP]; field_simp
  rw [hratio] at hbound
  set e := Real.exp (-(c₁ / (6 * δ))) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hKe : K * e ≤ Cs / 4 := by
    have h1' : e ≤ 1 / (c₁ / (6 * δ)) := exp_neg_le_inv (by positivity)
    have h2' : 1 / (c₁ / (6 * δ)) = 6 * δ / c₁ := by field_simp
    rw [h2'] at h1'
    have h3' : K * e ≤ K * (6 * δ / c₁) := mul_le_mul_of_nonneg_left h1' hK.le
    have h4' : K * (6 * δ / c₁) ≤ Cs / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hδ2
      rw [mul_div_assoc', div_le_iff₀ hc₁]
      nlinarith
    linarith
  set ρ := (k : ℝ) / (k.totient : ℝ) with hρ
  have hφ : (0 : ℝ) < (k.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le k
  have hsing := hS k hk1 hkeven
  have hre : (k : ℝ) * singularSeries k - K * ρ * X * e ≤
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have h := Complex.abs_re_le_norm
      (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ) - (((k : ℝ) * singularSeries k : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    have := (abs_le.mp (h.trans hbound)).1
    linarith
  have hmain : Cs / 4 * X ≤ (R1 (X ^ (6 * δ)) X ((k : ℕ) : ℤ)).re := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hA1 : (k : ℝ) * (Cs * ρ) ≤ (k : ℝ) * singularSeries k :=
      mul_le_mul_of_nonneg_left hsing hk0
    have hA2 : K * ρ * X * e ≤ ρ * X * (Cs / 4) := by
      have := mul_le_mul_of_nonneg_left hKe (by positivity : (0 : ℝ) ≤ ρ * X)
      nlinarith
    have hA3 : ρ * (Cs * (X / 2)) ≤ ρ * (Cs * k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkhalf.le hCs.le) (by positivity)
    have hA4 : Cs / 4 * X ≤ ρ * (Cs / 4 * X) := by
      have : 0 ≤ Cs / 4 * X := by positivity
      nlinarith
    nlinarith
  have hP0 : 0 ≤ X ^ (6 * δ) := Real.rpow_nonneg hX0.le _
  have hD : 0 ≤ divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by
    unfold divisorError
    apply add_nonneg
    · refine mul_nonneg ?_ (sum_nonneg (fun q _ => div_nonneg (by positivity) (by positivity)))
      simpa using div_nonneg zero_le_one hP0
    · refine mul_nonneg ?_ (tsum_nonneg (fun q => by split_ifs <;> positivity))
      simp
  have : 0 ≤ 1 * X * divisorError 1 (X ^ (6 * δ)) ((k : ℕ) : ℤ) := by positivity
  linarith

/-- Twin check: `leaf_absent_selected_of_small` has exactly the type of the open leaf
`Decomp559b.leaf_absent_selected`. -/
example (hL : Lemma2NoExcSmallDelta) (hS : SingularSeriesEvenLowerBP) : True :=
  let _f : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
    leaf_absent_selected_of_small hL hS
  trivial

#print axioms lemma2NoExcSmallDelta_of_BP
#print axioms leaf_absent_selected_of_small
#print axioms mv_617
#print axioms mv_71
#print axioms lemma2NoExcSmallDelta_of_leaves

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
