/-
Helfgott https://arxiv.org/abs/1312.7748v2 pages 50, 51 and 63.
Independent remainder moment split. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp580a
import LeanLab.Ternary.Decomp580b
import LeanLab.Ternary.Decomp580d

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The complementary circle domain with the exact open major arcs.
Helfgott page 10 equation 3.5 at delta zero eight and r zero 150000. -/
noncomputable def minorDomain (x : ℝ) : Set ℝ :=
  Set.Ioc (0 : ℝ) 1 \ (⋃ q : ℕ, ⋃ (_h : 1 ≤ q ∧ q ≤ Nat.gcd q 2 * 150000),
    ⋃ a : ℤ, ⋃ (_h : Int.gcd a q = 1),
      Set.Ioo ((a : ℝ) / q - (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x))
        ((a : ℝ) / q + (Nat.gcd q 2 * 8 * 150000 : ℝ) / (2 * q * x)))

/-- The large prime part of eta plus, with the paper cutoff p greater than sqrt x.
Helfgott page 50 proof of Theorem 6.3, definition of S one eta plus.
The von Mangoldt coefficient equals log p on prime indices. -/
noncomputable def primeSeries (x α : ℝ) : ℂ :=
  Task420.charSeries (fun n => if n.Prime ∧ Real.sqrt x < (n : ℝ) then
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
    else 0) α

/-- The remainder after removing the large prime part.
Helfgott page 50 proof of Theorem 6.3, definition of S two eta plus. -/
noncomputable def remainderSeries (x α : ℝ) : ℂ :=
  LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α x - primeSeries x α


/-- The coefficients removed from the large prime series.
Helfgott page 50 definition of S two eta plus. -/
noncomputable def remainderCoeff (x : ℝ) (n : ℕ) : ℂ :=
  if n.Prime ∧ Real.sqrt x < (n : ℝ) then 0 else
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)

/-- The removed coefficients remain absolutely summable.
Helfgott page 51 justification of the remainder Parseval step. -/
theorem remainderCoeff_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n => ‖remainderCoeff x n‖ := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (Task420.etaPlus_coefficients_summable hx)
  intro n
  unfold remainderCoeff
  split_ifs <;> simp <;> positivity

/-- The remainder is the character series of the removed coefficients.
Helfgott page 50 definition of S two and page 51 Parseval step. -/
theorem remainderSeries_eq_charSeries {x : ℝ} (hx : 0 < x) (α : ℝ) :
    remainderSeries x α = Task420.charSeries (remainderCoeff x) α := by
  have ha : Summable fun n : ℕ =>
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ := by
    simpa only [norm_mul, LeanLab.Ternary.MMS.norm_e, mul_one] using
      Task420.etaPlus_coefficients_summable hx
  have hp : Summable fun n : ℕ =>
      ‖(if n.Prime ∧ Real.sqrt x < (n : ℝ) then
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ) else 0) *
          LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ha
    intro n
    split_ifs <;> simp <;> positivity
  unfold remainderSeries primeSeries
  rw [Task420.S_eq_charSeries]
  unfold Task420.charSeries
  rw [← ha.of_norm.tsum_sub hp.of_norm]
  apply tsum_congr
  intro n
  unfold remainderCoeff
  split_ifs <;> simp

/-- LEAF. The nonprime indices have the stated coefficient square budget.
Helfgott v2 page 51 nonprime power estimate and book page 267 bounds for
C eta plus zero and one, combined on page 268 equation 14.28.
This excludes all prime indices and has no small prime contribution. -/
theorem nonprime_coeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, if ¬n.Prime then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x := by
  sorry

/-- LEAF. The indices at most sqrt x have the small coefficient square budget.
Helfgott v2 page 51 small index estimate, with the corrected coefficient
0.60581 from book page 268 before equation 14.28.
This contains no index above sqrt x and no eta star factor. -/
theorem small_index_coeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      0.60581 * Real.sqrt x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set S : ℝ := Real.sqrt x with hS
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg x
  have hS1 : 1 ≤ S := by
    rw [hS, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have hSsq : S ^ 2 = x := by rw [hS]; exact Real.sq_sqrt hx0.le
  have hSe : (1e13 : ℝ) ≤ S := by
    rw [hS]
    have h2 : (1e13 : ℝ) ^ 2 ≤ x := by norm_num; linarith
    calc (1e13 : ℝ) = Real.sqrt ((1e13 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h2
  -- the smooth weight has a linear majorant with constant below 11610
  have hC : 32 * Real.exp (3 / 2) * (200 / Real.pi) ≤ 11610 := by
    have hhalf : Real.exp (1 / 2) < 2 := by
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2), Real.exp_one_lt_d9, hsq]
    have he3 : Real.exp (3 / 2) ≤ 5.44 := by
      have hsplit : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
        rw [← Real.exp_add]; norm_num
      rw [hsplit]
      calc Real.exp 1 * Real.exp (1 / 2) ≤ 2.7182818286 * 2 := by
            exact mul_le_mul Real.exp_one_lt_d9.le hhalf.le (Real.exp_pos _).le (by norm_num)
        _ ≤ 5.44 := by norm_num
    rw [show 32 * Real.exp (3 / 2) * (200 / Real.pi) = 6400 * Real.exp (3 / 2) / Real.pi
      by ring]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three, he3, Real.exp_pos (3 / 2)]
  have hC16 : 16 * (11610 : ℝ) ^ 2 ≤ 0.60581 * S := by
    have h2 : (16 : ℝ) * 11610 ^ 2 ≤ 2.2e9 := by norm_num
    nlinarith [hSe]
  have h8C : 8 * (11610 : ℝ) ^ 2 * Real.log x ≤ 0.60581 * x := by
    have hLx : Real.log x ≤ 2 * S := by
      have hlogS : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos (by linarith)
      have hsplit : Real.log x = 2 * Real.log S := by
        rw [hS, Real.log_sqrt hx0.le]; ring
      rw [hsplit]; linarith
    have hstep : 8 * (11610 : ℝ) ^ 2 * Real.log x ≤ 8 * (11610 : ℝ) ^ 2 * (2 * S) :=
      mul_le_mul_of_nonneg_left hLx (by norm_num)
    have hfin : 16 * (11610 : ℝ) ^ 2 * S ≤ 0.60581 * x := by
      have hmono := mul_le_mul_of_nonneg_right hC16 hS0
      calc 16 * (11610 : ℝ) ^ 2 * S ≤ (0.60581 * S) * S := hmono
        _ = 0.60581 * S ^ 2 := by ring
        _ = 0.60581 * x := by rw [hSsq]
    nlinarith [hstep, hfin]
  -- pointwise coefficient bound
  have hterm : ∀ n : ℕ, (if (n : ℝ) ≤ S then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      (if (n : ℝ) ≤ S then (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 * ((n : ℝ) ^ 2 / x ^ 2)
        else 0) := by
    intro n
    by_cases hn : (n : ℝ) ≤ S
    · rw [if_pos hn, if_pos hn]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have ht : (0 : ℝ) ≤ (n : ℝ) / x := by positivity
      have hplus : |LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x)| ≤ 11610 * ((n : ℝ) / x) := by
        refine (Task420.etaPlus_gaussian_bound ht).trans ?_
        have hexp : Real.exp (-((n : ℝ) / x) ^ 2 / 2) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ((n : ℝ) / x)])
        calc (32 * Real.exp (3 / 2) * (200 / Real.pi)) * ((n : ℝ) / x) *
              Real.exp (-((n : ℝ) / x) ^ 2 / 2)
            ≤ 11610 * ((n : ℝ) / x) * 1 := by
              exact mul_le_mul (mul_le_mul_of_nonneg_right hC ht) hexp (Real.exp_pos _).le
                (by positivity)
          _ = 11610 * ((n : ℝ) / x) := by ring
      have hlogn : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log x := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simpa using Real.log_nonneg hx1
        · have hp : (0 : ℝ) < n := by exact_mod_cast hpos
          have hle : (n : ℝ) ≤ x := hn.trans (Real.sqrt_le_self_iff.mpr (Or.inr hx1))
          exact Real.log_le_log hp hle
      have hnorm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x) : ℂ)‖ ≤
          11610 * Real.log x * ((n : ℝ) / x) := by
        have h1 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x) : ℂ)‖ =
            (ArithmeticFunction.vonMangoldt n : ℝ) *
              |LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x)| := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]
        rw [h1]
        calc (ArithmeticFunction.vonMangoldt n : ℝ) *
              |LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x)|
            ≤ Real.log x * (11610 * ((n : ℝ) / x)) :=
              mul_le_mul hlogn hplus (abs_nonneg _) hlx.le
          _ = 11610 * Real.log x * ((n : ℝ) / x) := by ring
      calc ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x) : ℂ)‖ ^ 2
          ≤ (11610 * Real.log x * ((n : ℝ) / x)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ = (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 * ((n : ℝ) ^ 2 / x ^ 2) := by ring
    · rw [if_neg hn, if_neg hn]
  -- the summands vanish above sqrt x
  set N : ℕ := Nat.floor S + 1 with hN
  have hzero : ∀ n ∉ Finset.range N,
      (if (n : ℝ) ≤ S then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) = 0 := by
    intro n hn
    have hNn : N ≤ n := by
      simpa [Finset.mem_range, not_lt] using hn
    have hSN : ¬ (n : ℝ) ≤ S := by
      have h1 : S < (N : ℝ) := by
        rw [hN]; push_cast; exact Nat.lt_floor_add_one S
      have h2 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      intro hc; linarith
    simp [hSN]
  rw [tsum_eq_sum hzero]
  have hterm' : (Finset.range N).sum (fun n : ℕ => (if (n : ℝ) ≤ S then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0)) ≤
      (Finset.range N).sum (fun n : ℕ =>
        (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 * ((n : ℝ) ^ 2 / x ^ 2)) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases h : (n : ℝ) ≤ S
    · simpa [h] using hterm n
    · rw [if_neg h]; positivity
  refine hterm'.trans ?_
  have hfac : (Finset.range N).sum (fun n : ℕ =>
        (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 * ((n : ℝ) ^ 2 / x ^ 2)) =
      (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 *
        (Finset.range N).sum (fun n : ℕ => ((n : ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hfac]
  have hsum2 : (Finset.range N).sum (fun n : ℕ => ((n : ℝ) ^ 2)) ≤ (N : ℝ) ^ 3 := by
    have h1 : ∀ n ∈ Finset.range N, ((n : ℝ) ^ 2) ≤ (N : ℝ) ^ 2 := by
      intro n hn
      have hnN : n < N := Finset.mem_range.mp hn
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hnN.le) 2
    calc (Finset.range N).sum (fun n : ℕ => ((n : ℝ) ^ 2))
        ≤ (Finset.range N).sum (fun _n : ℕ => ((N : ℝ) ^ 2)) := Finset.sum_le_sum h1
      _ = (N : ℝ) * (N : ℝ) ^ 2 := by simp
      _ = (N : ℝ) ^ 3 := by ring
  have hNle : (N : ℝ) ≤ 2 * S := by
    have h1 : ((Nat.floor S : ℕ) : ℝ) ≤ S := Nat.floor_le hS0
    have h2 : (N : ℝ) = ((Nat.floor S : ℕ) : ℝ) + 1 := by rw [hN]; push_cast; ring
    linarith
  have hN3 : (N : ℝ) ^ 3 ≤ 8 * S ^ 3 := by
    calc (N : ℝ) ^ 3 ≤ (2 * S) ^ 3 := pow_le_pow_left₀ (by positivity) hNle 3
      _ = 8 * S ^ 3 := by ring
  have hS3 : S ^ 3 = S * x := by
    calc S ^ 3 = S ^ 2 * S := by ring
      _ = x * S := by rw [hSsq]
      _ = S * x := by ring
  have hCnn : (0 : ℝ) ≤ (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 := by positivity
  have hfinal : (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 * (8 * S ^ 3) ≤
      0.60581 * S * Real.log x := by
    rw [hS3, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
    calc (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 * (8 * (S * x))
        = (8 * (11610 : ℝ) ^ 2 * Real.log x) * (Real.log x * S * x) := by ring
      _ ≤ (0.60581 * x) * (Real.log x * S * x) :=
          mul_le_mul_of_nonneg_right h8C (by positivity)
      _ = 0.60581 * S * Real.log x * x ^ 2 := by ring
  calc (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 *
        (Finset.range N).sum (fun n : ℕ => ((n : ℝ) ^ 2))
      ≤ (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 * (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hsum2 hCnn
    _ ≤ (11610 : ℝ) ^ 2 * (Real.log x) ^ 2 / x ^ 2 * (8 * S ^ 3) :=
        mul_le_mul_of_nonneg_left hN3 hCnn
    _ ≤ 0.60581 * S * Real.log x := hfinal

/-- The two arithmetic coefficient bounds give the required E budget.
Helfgott page 63 equation 7.26 and book page 268 equation 14.28.
CONDITIONAL ON nonprime_coeff_square_upper and small_index_coeff_square_upper. -/
theorem remainderCoeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, ‖remainderCoeff x n‖ ^ 2) ≤ 8.4031e-12 * x := by
  have hx0 : 0 < x := by linarith
  let c : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)
  have hc : Summable fun n => ‖c n‖ := Task420.etaPlus_coefficients_summable hx0
  have hdiag : Function.Injective (fun n : ℕ => (n, n)) := by
    intro m n h
    exact (Prod.mk.inj h).1
  have hcsq : Summable fun n => ‖c n‖ ^ 2 := by
    simpa only [Function.comp_def, norm_mul, ← pow_two] using
      (hc.mul_norm hc).comp_injective hdiag
  have hnp : Summable fun n => if ¬n.Prime then ‖c n‖ ^ 2 else 0 := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hcsq
    intro n
    split_ifs <;> simp <;> positivity
  have hsmall : Summable fun n : ℕ => if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0 := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ hcsq
    intro n
    split_ifs <;> simp <;> positivity
  have hrem : Summable fun n => ‖remainderCoeff x n‖ ^ 2 := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hcsq
    intro n
    unfold remainderCoeff
    split_ifs <;> simp [c] <;> positivity
  have hpoint (n : ℕ) : ‖remainderCoeff x n‖ ^ 2 ≤
      (if ¬n.Prime then ‖c n‖ ^ 2 else 0) +
        (if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0) := by
    by_cases hp : n.Prime
    · by_cases hs : (n : ℝ) ≤ Real.sqrt x
      · simp [remainderCoeff, c, hp, hs, not_lt.mpr hs]
      · simp [remainderCoeff, hp, hs, lt_of_not_ge hs]
    · by_cases hs : (n : ℝ) ≤ Real.sqrt x
      · simp [remainderCoeff, c, hp, hs]
        positivity
      · simp [remainderCoeff, c, hp, hs]
  have hsum := hrem.tsum_le_tsum hpoint (hnp.add hsmall)
  rw [hnp.tsum_add hsmall] at hsum
  have harith := add_le_add (nonprime_coeff_square_upper x hx)
    (small_index_coeff_square_upper x hx)
  calc
    _ ≤ (∑' n : ℕ, if ¬n.Prime then ‖c n‖ ^ 2 else 0) +
        (∑' n : ℕ, if (n : ℝ) ≤ Real.sqrt x then ‖c n‖ ^ 2 else 0) := hsum
    _ ≤ (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x +
        0.60581 * Real.sqrt x * Real.log x := harith
    _ = (2.94325 * Real.log x + 5.12425) * Real.sqrt x := by ring
    _ ≤ (2.94325 * Real.log x + 5.12426) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x)
    _ ≤ 8.4029e-12 * x := book_E_bound hx
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) hx0.le

/-- Parseval converts the removed coefficient budget into the full circle L2 bound.
Helfgott page 51 last display and page 63 equation 7.26.
CONDITIONAL ON the two arithmetic coefficient leaves. -/
theorem remainder_circle_l2 (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖remainderSeries x α‖ ^ 2) ≤ 8.4031e-12 * x := by
  have hx0 : 0 < x := by linarith
  simp_rw [remainderSeries_eq_charSeries hx0]
  rw [charSeries_parseval _ (remainderCoeff_summable hx0)]
  exact remainderCoeff_square_upper x hx

/-- The remainder series is continuous at positive scales.
Helfgott page 51 justification of integration over the circle. -/
theorem remainderSeries_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (remainderSeries x) := by
  have h := Task420.continuous_charSeries _ (remainderCoeff_summable hx)
  have heq : remainderSeries x = Task420.charSeries (remainderCoeff x) :=
    funext (remainderSeries_eq_charSeries hx)
  rw [heq]
  exact h

/-- The star norm weight is continuous at positive scales.
Helfgott page 50 weighted triangle step. -/
theorem starNorm_continuous {x : ℝ} (hx : 0 < x) : Continuous (starNorm x) := by
  unfold starNorm starWeight
  simp_rw [Task420.S_eq_charSeries]
  exact (Task420.continuous_charSeries _ (Task420.etaStar_coefficients_summable hx)).norm

/-- The two independent smaller leaves supply the exact remainder moment budget.
Helfgott page 51 last display and page 63 equation 7.27.
CONDITIONAL ON star_mass_error and the two arithmetic coefficient leaves.
The definitions unfold to the assigned sealed remainder statement. -/
theorem remainder_moment_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∫ α in minorDomain x, starNorm x α * ‖remainderSeries x α‖ ^ 2) ≤
      1.0532e-11 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
  have hx0 : 0 < x := by linarith
  let C := (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / LeanLab.Helfgott2013.κ
  have hC : 0 ≤ C := by dsimp [C, LeanLab.Helfgott2013.κ]; positivity
  have hi : IntegrableOn (fun α => ‖remainderSeries x α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    ((remainderSeries_continuous hx0).norm.pow 2).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hsub : minorDomain x ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  have hmono := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun α => sq_nonneg ‖remainderSeries x α‖))
    (Filter.Eventually.of_forall hsub)
  have hweighted : IntegrableOn (fun α => starNorm x α * ‖remainderSeries x α‖ ^ 2)
      (minorDomain x) :=
    (((starNorm_continuous hx0).mul ((remainderSeries_continuous hx0).norm.pow 2)).integrableOn_Icc).mono_set
      (hsub.trans Set.Ioc_subset_Icc_self)
  have hle := integral_mono hweighted ((hi.mono_set hsub).const_mul C)
    (fun α => mul_le_mul_of_nonneg_right (starNorm_uniform x hx α) (sq_nonneg _))
  rw [integral_const_mul] at hle
  calc
    _ ≤ C * (∫ α in minorDomain x, ‖remainderSeries x α‖ ^ 2) := hle
    _ ≤ C * (∫ α in Set.Ioc (0 : ℝ) 1, ‖remainderSeries x α‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmono hC
    _ ≤ C * (8.4031e-12 * x) :=
      mul_le_mul_of_nonneg_left (remainder_circle_l2 x hx) hC
    _ = ((Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12) *
        (x ^ 2 / LeanLab.Helfgott2013.κ) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right LeanLab.Helfgott2013.SE_coeff
      (by unfold LeanLab.Helfgott2013.κ; positivity)

/-- The copied minor domain equals the complement of the real radius arcs.
Helfgott page 10 equation 3.5 at delta eight and radius 150000. -/
theorem minorDomain_eq_majorArcs_complement (x : ℝ) :
    minorDomain x = Set.Ioc (0 : ℝ) 1 \ majorArcs x 8 150000 := by
  have hbound (q : ℕ) : q ≤ Nat.gcd q 2 * 150000 ↔
      (q : ℝ) ≤ Nat.gcd q 2 * 150000 := by norm_cast
  ext α
  simp only [minorDomain, majorArcs, Set.mem_sdiff, Set.mem_iUnion, hbound]

/-- The exact minor domain is measurable.
Helfgott page 50 weighted moments outside the open arcs. -/
theorem minorDomain_measurable (x : ℝ) : MeasurableSet (minorDomain x) := by
  rw [minorDomain_eq_majorArcs_complement]
  exact measurableSet_Ioc.diff (majorArcs_isOpen x 8 150000).measurableSet

end LeanLab.Ternary.Task580
