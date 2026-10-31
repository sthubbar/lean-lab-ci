/-
AI wrote this Lean code. Codex task120, 2026-10-26.
Lemma 3.1, P0097, pages 349 to 352.
The analytic approximation remains CONDITIONAL.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ArcArithmetic
import LeanLab.Zinoviev1997.ModelFormula
import LeanLab.Zinoviev1997.State1546

namespace LeanLab.Zinoviev1997.Decomp120
open Real Finset ArithmeticFunction LeanLab.CircleOrth MeasureTheory
open scoped ArithmeticFunction.Moebius

/-- The continuous model on page 352, evaluated as exp of minus 3x over x. -/
noncomputable def continuousModel (N : ℕ) (z : ℝ) : ℂ :=
  let x : ℂ := (1 / (N : ℝ) : ℝ) + 2 * Real.pi * Complex.I * z
  Complex.exp (-3 * x) / x

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem reciprocal_model_error (x : ℂ) (hx : x ≠ 0) (hsmall : ‖x‖ ≤ 1 / 2) :
    ‖1 / x - 1 / (1 - Complex.exp (-x))‖ ≤ 2 := by
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : ‖Complex.exp (-x) - 1 + x‖ ≤ ‖x‖ ^ 2 := by
    simpa using Complex.norm_exp_sub_one_sub_id_le (x := -x) (by simpa using (show ‖x‖ ≤ 1 by linarith))
  have hlo : ‖x‖ - ‖x‖ ^ 2 ≤ ‖1 - Complex.exp (-x)‖ := by
    have hh := norm_sub_norm_le x (1 - Complex.exp (-x))
    have he : x - (1 - Complex.exp (-x)) = Complex.exp (-x) - 1 + x := by ring
    rw [he] at hh
    linarith
  have hdpos : 0 < ‖1 - Complex.exp (-x)‖ := by nlinarith
  have hd : 1 - Complex.exp (-x) ≠ 0 := norm_pos_iff.mp hdpos
  have he : 1 / x - 1 / (1 - Complex.exp (-x)) =
      -(Complex.exp (-x) - 1 + x) / (x * (1 - Complex.exp (-x))) := by
    field_simp
    <;> ring
  rw [he, norm_div, norm_neg, norm_mul, div_le_iff₀ (mul_pos ht hdpos)]
  nlinarith [mul_le_mul_of_nonneg_left hlo ht.le]

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem major_arc_exponent_small (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z‖ ≤ 1 / 2 := by
  have hn : (0 : ℝ) < N := by linarith
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hs : (100 : ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt (by norm_num) hn.le).mpr (by linarith)
  have hlog : Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hz' : |z| ≤ 2 * Real.log N / N := by
    refine hz.trans ?_
    unfold arcRadius
    apply div_le_div_of_nonneg_left (by positivity) hn
    nlinarith
  have hnorm : ‖(2 : ℂ) * Real.pi * Complex.I * z‖ = 2 * Real.pi * |z| := by
    simp [norm_mul, Real.pi_pos.le, abs_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ)‖ + ‖(2 : ℂ) * Real.pi * Complex.I * z‖ := norm_add_le _ _
    _ = 1 / (N : ℝ) + 2 * Real.pi * |z| := by
      rw [hnorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 1 / (N : ℝ) + 2 * Real.pi * (2 * Real.log N / N) := by gcongr
    _ ≤ 1 / 2 := by
      have hsq := Real.sq_sqrt hn.le
      have hp := Real.pi_lt_four
      suffices hh : 1 + 2 * Real.pi * (2 * Real.log N) ≤ (1 / 2 : ℝ) * N by
        calc
          _ = (1 + 2 * Real.pi * (2 * Real.log N)) / N := by ring
          _ ≤ 1 / 2 := (div_le_iff₀ hn).mpr hh
      have hh : 2 * Real.pi * (2 * Real.log N) ≤ 32 * Real.sqrt N := by
        nlinarith [mul_le_mul_of_nonneg_right hp.le hl]
      nlinarith

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem ratio_eq_exp (N : ℕ) (z : ℝ) :
    modelRatio N (-z) = Complex.exp
      (-((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z))) := by
  unfold modelRatio LeanLab.CircleOrth.ee
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The prime tail T of display 3.1, with the lab's reflected Fourier sign. -/
noncomputable def residueTail (N q l : ℕ) (z : ℝ) : ℂ := by
  classical
  exact ∑' n : ℕ, if n.Prime ∧ Real.sqrt N < n ∧ n % q = l % q then
    ((Real.log n * Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) * ee (-(n : ℝ) * z) else 0

/-- The reduced residue expansion in display 3.1 on page 349. -/
noncomputable def residueExpansion (N q a : ℕ) (z : ℝ) : ℂ :=
  ∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
    ee (-((a : ℝ) * l / q)) * residueTail N q l z

/-- LEAF. Display 3.1, page 349, prime power and small prime reduction.
The larger remainder sqrt N times log squared N is a supporting variant of the printed
sqrt N remainder. The cited Lemma31Input is unchanged. -/
theorem prime_reduction (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z‖ ≤
      Real.sqrt N * Real.log N ^ 2 := by
  sorry

/-- LEAF. Displays 3.2 to 3.4, pages 349 to 351, and the Ramanujan identity on page 351.
Partial summation from Proposition 1.4 and the two integrated remainders give this bound.
The constant 3.8 leaves room above the displayed 2.99, 0.14 and 0.001 estimates. -/
theorem residue_integral_approximation (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖residueExpansion N q a z -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ ≤
        3.8 * lemma31Base N q := by
  sorry

/-- LEAF. Page 352, the conclusion of displays 3.1 to 3.4 and the Ramanujan identity.
This analytic leaf includes partial summation from Proposition 1.4, pages 349 to 351.
CONDITIONAL ON the unproved analytic estimates. -/
theorem continuous_approximation (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ ≤
        3.9 * lemma31Base N q := by
  have hlog : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hb : Real.sqrt N * Real.log N ^ 2 ≤ 0.1 * lemma31Base N q := by
    have hφ : (0 : ℝ) ≤ Nat.totient q := Nat.cast_nonneg _
    have hp := Real.pi_gt_three
    have hf : 10 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hf
      (show 0 ≤ Real.sqrt N * Real.log N ^ 2 by positivity)
    unfold lemma31Base
    nlinarith
  calc
    _ ≤ ‖SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z‖ +
        ‖residueExpansion N q a z -
          (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ :=
      by
        have he : SZ N (-((a : ℝ) / q + z)) -
            (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z =
            (SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z) +
            (residueExpansion N q a z -
              (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z) := by ring
        rw [he]
        exact norm_add_le _ _
    _ ≤ Real.sqrt N * Real.log N ^ 2 + 3.8 * lemma31Base N q :=
      add_le_add (prime_reduction N hN q hq a ha hac z hz)
        (residue_integral_approximation N hN hG q hq a ha hac z hz)
    _ ≤ _ := by linarith

/-- LEAF. Page 352, the final integral to geometric series comparison. -/
theorem continuous_model_error (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖continuousModel N z - modelSum N (-z)‖ ≤ 4 := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  have hn : (0 : ℝ) < N := by linarith
  have hn' : 0 < N := by exact_mod_cast hn
  have hxre : x.re = 1 / (N : ℝ) := by simp [x]
  have hxpos : 0 < x.re := by rw [hxre]; positivity
  have hx : x ≠ 0 := by intro h; rw [h] at hxpos; simpa using hxpos
  have hsmall : ‖x‖ ≤ 1 / 2 :=
    major_arc_exponent_small N hN q (Finset.mem_Icc.mp hq).1 z hz
  have hrec := reciprocal_model_error x hx hsmall
  have hmodel : modelSum N (-z) = Complex.exp (-3 * x) / (1 - Complex.exp (-x)) := by
    rw [modelSum_geometric N hn', ratio_eq_exp]
    change Complex.exp (-x) ^ 3 / _ = _
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hexp : ‖Complex.exp (-3 * x)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith
  have he : continuousModel N z - modelSum N (-z) =
      Complex.exp (-3 * x) * (1 / x - 1 / (1 - Complex.exp (-x))) := by
    rw [hmodel]
    change Complex.exp (-3 * x) / x - _ = _
    ring
  rw [he, norm_mul]
  have : ‖Complex.exp (-3 * x)‖ * ‖1 / x - 1 / (1 - Complex.exp (-x))‖ ≤ 1 * 2 :=
    mul_le_mul hexp hrec (norm_nonneg _) (by norm_num)
  linarith

/-- LEAF. Page 352, scalar slack between 3.9 and 4 absorbs the model error. -/
theorem closing_budget (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) :
    3.9 * lemma31Base N q + 4 / (Nat.totient q : ℝ) ≤ 4 * lemma31Base N q := by
  have hn : (1 : ℝ) ≤ N := by linarith
  have hlog : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hs : 1 ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hdiv : 4 / (Nat.totient q : ℝ) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hb : 40 ≤ lemma31Base N q := by
    unfold lemma31Base
    have hfirst : 1 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N := by
      have := Real.pi_pos
      nlinarith
    have hprod : 1 ≤ ((Nat.totient q : ℝ) + 4 * Real.pi * Real.log N) * Real.sqrt N :=
      by nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N)]
    nlinarith [mul_le_mul_of_nonneg_right hprod (sq_nonneg (Real.log N))]
  linarith

/-- Lemma 3.1 assembled with exactly the existing cited Prop conclusion.
CONDITIONAL ON the analytic leaves. The assembly contains no sorry. -/
theorem lemma31 (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH) : Lemma31Input N := by
  intro q hq a ha hac z hz
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hdiff := continuous_model_error N hN q hq z hz
  have hcoef := norm_moebius_ratio q hq0
  have he : SZ N (-((a : ℝ) / q + z)) -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * modelSum N (-z) =
      (SZ N (-((a : ℝ) / q + z)) -
        (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z) +
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) *
        (continuousModel N z - modelSum N (-z)) := by ring
  rw [he]
  refine (norm_add_le _ _).trans ((add_le_add
    (continuous_approximation N hN hG q hq a ha hac z hz) ?_).trans
      (closing_budget N hN q hq0))
  rw [norm_mul]
  calc
    _ ≤ (1 / (Nat.totient q : ℝ)) * 4 :=
      mul_le_mul hcoef hdiff (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A negative diagnostic for display 1.7 on page 338.
Replacing von Mangoldt by log n already exceeds the target at cutoff 11. -/
theorem log_majorant_exceeds_budget : (0.61 : ℝ) < ∑ n ∈ Finset.range 11, Real.log n / (n : ℝ) ^ 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := Real.log_four_eq
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h7 : Real.log (5 : ℝ) ≤ Real.log 7 := Real.log_le_log (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, h4, h6, h8, h9, Real.log_ten_eq]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

end LeanLab.Zinoviev1997.Decomp120
