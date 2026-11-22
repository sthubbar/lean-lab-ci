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

/-! ### Helper estimates for the nonprime coefficient square budget -/

/-- The coefficient norm is the von Mangoldt value times the weight modulus. -/
private theorem npe_coeff_norm (x : ℝ) (n : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x) : ℂ)‖ =
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        |LeanLab.HelfgottArcs.etaPlus ((n : ℝ) / x)| := by
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]

/-- A nonprime prime power has its von Mangoldt square below half its log weight. -/
private theorem npe_mangoldt_sq (n : ℕ) (hnp : ¬ n.Prime) :
    (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log n / 2 := by
  by_cases h0 : ArithmeticFunction.vonMangoldt n = 0
  · rw [h0]; ring_nf; positivity
  · obtain ⟨p, k, hp, hpk⟩ := (isPrimePow_iff_pow_succ n).mp
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0)
    have hple : Nat.Prime p := Nat.prime_iff.mpr hp
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso; apply hnp; rw [← hpk, h, pow_one]; exact hple
      · exact h
    have hL : ArithmeticFunction.vonMangoldt n = Real.log p := by
      rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
        ArithmeticFunction.vonMangoldt_apply_prime hple]
    have hlogn : Real.log n = ((k : ℝ) + 1) * Real.log p := by
      rw [← hpk, Nat.cast_pow, Real.log_pow]; push_cast; ring
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hple.one_lt)
    have hk2 : (2:ℝ) ≤ (k:ℝ) + 1 := by
      have : (1:ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    rw [hL, hlogn]
    nlinarith [hlogp, sq_nonneg (Real.log p)]

open Finset in
/-- The nonprime von Mangoldt mass is psi minus theta. -/
private theorem npe_mass_identity (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
        if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) =
      Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc (N : ℝ), Chebyshev.theta_eq_sum_Icc (N : ℝ)]
  simp only [Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_filter]
  have hpt : ∀ n : ℕ,
      (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) =
        (ArithmeticFunction.vonMangoldt n : ℝ) - (if n.Prime then Real.log n else 0) := by
    intro n
    by_cases hn : n.Prime
    · simp [hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
    · simp [hn]
  simp only [hpt, sum_sub_distrib]

open Finset in
/-- The nonprime von Mangoldt mass is at most 1.251 times the square root. -/
private theorem npe_mass_le (N : ℕ) (hN : (10:ℝ)^8 ≤ (N:ℝ)) :
    (∑ n ∈ Finset.range (N + 1),
        if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) ≤
      1.251 * Real.sqrt (N : ℝ) := by
  rw [npe_mass_identity]
  have h := LeanLab.Common.PsiTheta.psi_sub_theta_lt_125 hN
  have hs : (0:ℝ) ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
  linarith

/-- The truncated log is at most the log of seven times the scale. -/
private theorem npe_log_le (x : ℝ) (hx : 1 ≤ x) {n : ℕ} (hn : n ≤ Nat.ceil (6*x)) :
    Real.log (n : ℝ) ≤ Real.log (7*x) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h]; norm_num
    exact (Real.log_pos (by linarith)).le
  · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
    have h1 : (n:ℝ) ≤ (Nat.ceil (6*x) : ℝ) := by exact_mod_cast hn
    have h2 : (Nat.ceil (6*x) : ℝ) < 6*x + 1 := Nat.ceil_lt_add_one (by linarith)
    have : (n:ℝ) ≤ 7*x := by linarith
    exact Real.log_le_log hnpos this

/-- For arguments above two the cube times Gaussian is antitone. -/
private theorem npe_cube_exp_anti {v u : ℝ} (hv : 2 ≤ v) (hvu : v ≤ u) :
    u^3 * Real.exp (-(u^2)) ≤ v^3 * Real.exp (-(v^2)) := by
  rcases eq_or_lt_of_le hvu with h | h
  · rw [← h]
  · have hv0 : (0:ℝ) < v := by linarith
    have hlog : Real.log (u/v) ≤ (u - v)/v := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) hv0)
      rw [div_sub_one (ne_of_gt hv0)] at h1
      exact h1
    have h3 : 3 * Real.log (u/v) ≤ u^2 - v^2 := by
      have h2 : 3 * ((u - v)/v) ≤ u^2 - v^2 := by
        rw [show (3:ℝ) * ((u - v)/v) = 3*(u-v)/v by ring, div_le_iff₀ hv0]
        have hp1 : (0:ℝ) ≤ u - v := by linarith
        have hp2 : (0:ℝ) ≤ v*(u+v) - 3 := by nlinarith
        have hp3 : (0:ℝ) ≤ (u-v) * (v*(u+v) - 3) := mul_nonneg hp1 hp2
        nlinarith [hp3]
      nlinarith [hlog]
    have hexp : (u/v)^3 ≤ Real.exp (u^2 - v^2) := by
      have h4 := Real.exp_le_exp.mpr h3
      have h5 : Real.exp (3 * Real.log (u/v)) = (u/v)^3 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.exp_nat_mul,
          Real.exp_log (div_pos (by linarith) hv0)]
      rwa [h5] at h4
    have hu3 : v^3 * (u/v)^3 = u^3 := by
      rw [div_pow]
      exact mul_div_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hv0))
    have hfin : (u/v)^3 * Real.exp (-(u^2)) ≤ Real.exp (-(v^2)) := by
      have h6 : Real.exp (u^2 - v^2) * Real.exp (-(u^2)) = Real.exp (-(v^2)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (u/v)^3 * Real.exp (-(u^2)) ≤ Real.exp (u^2 - v^2) * Real.exp (-(u^2)) :=
            mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
        _ = Real.exp (-(v^2)) := h6
    calc u^3 * Real.exp (-(u^2)) = v^3 * ((u/v)^3 * Real.exp (-(u^2))) := by
          rw [← mul_assoc, hu3]
      _ ≤ v^3 * Real.exp (-(v^2)) := mul_le_mul_of_nonneg_left hfin (by positivity)

/-- The indices below six times the scale have the stated coefficient square budget. -/
private theorem npe_part1 (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑ n ∈ Finset.range (Nat.ceil (6*x) + 1),
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      ≤ 2 * Real.log (7*x) * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlog7 : (0:ℝ) ≤ Real.log (7*x) := Real.log_nonneg (by linarith)
  have hM1e8 : (10:ℝ)^8 ≤ ((Nat.ceil (6*x) : ℕ) : ℝ) := by
    have h : (6*x : ℝ) ≤ (Nat.ceil (6*x) : ℝ) := Nat.le_ceil (6*x)
    nlinarith
  have hpt : ∀ n ∈ Finset.range (Nat.ceil (6*x) + 1),
      (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0) ≤
      (1.16631 * Real.log (7*x) / 2) *
        (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
    intro n hn
    have hnM : n ≤ Nat.ceil (6*x) := by
      have := Finset.mem_range.mp hn; omega
    by_cases hnp : n.Prime
    · simp [hnp]
    · rw [if_pos hnp, if_pos hnp]
      rw [npe_coeff_norm, mul_pow]
      have hη : |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)| ≤ 1.079955 :=
        EtaBound379.etaPlus_abs_le _
      have hη0 : (0:ℝ) ≤ |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)| := abs_nonneg _
      have hη2 : |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)|^2 ≤ 1.16631 := by
        nlinarith [hη, hη0]
      have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hsq : (ArithmeticFunction.vonMangoldt n : ℝ)^2 ≤
          (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (7*x) / 2 := by
        have h1 := npe_mangoldt_sq n hnp
        have h2 := npe_log_le x hx1 hnM
        nlinarith [hΛ, h1, h2]
      calc (ArithmeticFunction.vonMangoldt n : ℝ)^2 *
            |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)|^2
          ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (7*x) / 2) * 1.16631 :=
            mul_le_mul hsq hη2 (by positivity) (by positivity)
        _ = 1.16631 * Real.log (7*x) / 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by ring
  have hmass := npe_mass_le (Nat.ceil (6*x)) hM1e8
  calc (∑ n ∈ Finset.range (Nat.ceil (6*x) + 1),
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      ≤ ∑ n ∈ Finset.range (Nat.ceil (6*x) + 1),
          (1.16631 * Real.log (7*x) / 2) *
            (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = (1.16631 * Real.log (7*x) / 2) *
          ∑ n ∈ Finset.range (Nat.ceil (6*x) + 1),
            (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (1.16631 * Real.log (7*x) / 2) * (1.251 * Real.sqrt ((Nat.ceil (6*x):ℕ):ℝ)) := by
        apply mul_le_mul_of_nonneg_left hmass
        positivity
    _ ≤ 2 * Real.log (7*x) * Real.sqrt x := by
        have hMle : ((Nat.ceil (6*x) : ℕ) : ℝ) ≤ 7*x := by
          have h : (Nat.ceil (6*x) : ℝ) < 6*x + 1 := Nat.ceil_lt_add_one (by linarith)
          linarith
        have hsM : Real.sqrt ((Nat.ceil (6*x):ℕ):ℝ) ≤ Real.sqrt (7*x) := Real.sqrt_le_sqrt hMle
        have hsqrt7 : Real.sqrt 7 ≤ 2.7 := by
          rw [Real.sqrt_le_iff]; constructor <;> norm_num
        have hsx : Real.sqrt x * Real.sqrt 7 = Real.sqrt (7*x) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 7)]; ring
        have hs0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
        have hL0 : (0:ℝ) ≤ Real.log (7*x) := hlog7
        have hsq7 : Real.sqrt (7*x) ≤ 2.7 * Real.sqrt x := by
          rw [← hsx]; nlinarith
        calc (1.16631 * Real.log (7*x) / 2) * (1.251 * Real.sqrt ((Nat.ceil (6*x):ℕ):ℝ))
            ≤ (1.16631 * Real.log (7*x) / 2) * (1.251 * (2.7 * Real.sqrt x)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (hsM.trans hsq7) (by norm_num)
          _ ≤ 2 * Real.log (7*x) * Real.sqrt x := by
              nlinarith [hL0, hs0]

set_option maxHeartbeats 2000000 in
/-- The tail beyond six times the scale has a negligible coefficient square budget. -/
private theorem npe_tail (x : ℝ) (hx : 4.9e26 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.Ico (Nat.ceil (6*x) + 1) N,
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      ≤ 0.0001 * Real.log x * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) he
  have hlogx0 : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hlogx1
  set K : ℕ := Nat.ceil (6*x) + 1 with hK
  have hKval : (K:ℝ) = (Nat.ceil (6*x) : ℝ) + 1 := by rw [hK]; push_cast; ring
  have hKgt : (6*x) < (K:ℝ) := by
    have h1 : (6*x : ℝ) ≤ (Nat.ceil (6*x) : ℝ) := Nat.le_ceil (6*x)
    linarith
  have hKle : (K:ℝ) ≤ 7*x := by
    have h1 : (Nat.ceil (6*x) : ℝ) < 6*x + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hKn : (10:ℝ)^8 ≤ (K:ℝ) := by
    have h1 : (6*x : ℝ) ≤ (Nat.ceil (6*x) : ℝ) := Nat.le_ceil (6*x)
    linarith
  have ht2 : ∀ n : ℕ, K ≤ n → (2:ℝ) ≤ (n:ℝ)/x := by
    intro n hn
    have h1 : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hx0]; linarith
  set C1 : ℝ := 32 * Real.exp (3/2) * (200/Real.pi) with hC1
  have hC1nn : (0:ℝ) ≤ C1 := by rw [hC1]; positivity
  have hC1le : C1 ≤ 11610 := by
    rw [hC1]
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
    rw [show 32 * Real.exp (3 / 2) * (200 / Real.pi) = 6400 * Real.exp (3 / 2) / Real.pi by ring]
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three, he3, Real.exp_pos (3 / 2)]
  have hC1sq : C1^2 ≤ 1.348e8 := by nlinarith [hC1nn, hC1le]
  set g : ℕ → ℝ := fun n =>
    Real.log x * C1^2 / 2 * (((n:ℝ)/x)^3 * Real.exp (-((n:ℝ)/x)^2)) with hg
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    have := Real.exp_pos (-((n:ℝ)/x)^2)
    positivity
  have hganti : ∀ {m n : ℕ}, K ≤ m → m ≤ n → g n ≤ g m := by
    intro m n hm hmn
    have hm2 : (2:ℝ) ≤ (m:ℝ)/x := ht2 m hm
    have hle : (m:ℝ)/x ≤ (n:ℝ)/x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      exact_mod_cast hmn
    have hkey := npe_cube_exp_anti hm2 hle
    rw [hg]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hgdouble : ∀ m : ℕ, K ≤ m → g (2*m) ≤ g m / 4 := by
    intro m hm
    set t : ℝ := (m:ℝ)/x with ht
    have ht2m : (2:ℝ) ≤ t := by rw [ht]; exact ht2 m hm
    have h32 : 32 ≤ Real.exp (3*t^2) := by
      have h1 : 1 + t^2 ≤ Real.exp (t^2) := by linarith [Real.add_one_le_exp (t^2)]
      have h3 : Real.exp (3*t^2) = (Real.exp (t^2))^3 := by
        rw [show (3:ℝ)*t^2 = ((3:ℕ):ℝ)*t^2 by norm_num, Real.exp_nat_mul]
      rw [h3]
      have h5 : (5:ℝ) ≤ Real.exp (t^2) := by nlinarith [sq_nonneg t]
      have h125 : (125:ℝ) ≤ (Real.exp (t^2))^3 := by
        have h6 := pow_le_pow_left₀ (show (0:ℝ) ≤ 5 by norm_num) h5 3
        norm_num at h6 ⊢
        exact h6
      linarith
    have hstep : 8 * Real.exp (-((2*t)^2)) ≤ Real.exp (-(t^2)) / 4 := by
      have hE : (0:ℝ) < Real.exp (-((2*t)^2)) := Real.exp_pos _
      have h1 : Real.exp (-(t^2)) = Real.exp (3*t^2) * Real.exp (-((2*t)^2)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h1]
      have hp : (0:ℝ) ≤ (Real.exp (3*t^2) - 32) * Real.exp (-((2*t)^2)) :=
        mul_nonneg (by linarith) hE.le
      nlinarith [hp]
    have hgm : g m = Real.log x * C1^2 / 2 * (t^3 * Real.exp (-(t^2))) := by
      rw [hg, ht]
    rw [hg]
    have hcast : (((2*m : ℕ)) : ℝ) = 2*(m:ℝ) := by push_cast; ring
    have ht2' : ((2*(m:ℝ))/x) = 2*t := by rw [ht]; ring
    calc Real.log x * C1^2/2 *
          (((((2*m:ℕ):ℝ)/x))^3 * Real.exp (-(((((2*m:ℕ):ℝ)/x)))^2))
        = Real.log x * C1^2/2 * (8 * (t^3 * Real.exp (-((2*t)^2)))) := by
            rw [hcast, ht2']; ring
      _ ≤ Real.log x * C1^2/2 * (t^3 * Real.exp (-(t^2)) / 4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have ht3 : (0:ℝ) ≤ t^3 := by positivity
            nlinarith [hstep, ht3]
      _ = (Real.log x * C1^2/2 * (t^3 * Real.exp (-(t^2)))) / 4 := by ring
      _ = g m / 4 := by rw [hgm]
  have hgiter : ∀ L : ℕ, g (K * 2^L) ≤ (1/4:ℝ)^L * g K := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
        have h1 : K * 2^(L+1) = 2 * (K * 2^L) := by ring
        have h2 : K ≤ K * 2^L := Nat.le_mul_of_pos_right K (pow_pos (by norm_num) L)
        rw [h1]
        calc g (2 * (K * 2^L)) ≤ g (K * 2^L) / 4 := hgdouble _ h2
          _ ≤ ((1/4:ℝ)^L * g K) / 4 := div_le_div_of_nonneg_right ih (by norm_num)
          _ = (1/4:ℝ)^(L+1) * g K := by ring
  have hgeom : ∀ L : ℕ, (∑ j ∈ Finset.range L, (1/2:ℝ)^j) ≤ 2 := by
    intro L
    have hmain : ∀ L : ℕ, (∑ j ∈ Finset.range L, (1/2:ℝ)^j) ≤ 2 - 2*(1/2:ℝ)^L := by
      intro L
      induction L with
      | zero => simp
      | succ L ih =>
          rw [Finset.sum_range_succ]
          have h2 : 2*(1/2:ℝ)^(L+1) = (1/2:ℝ)^L := by rw [pow_succ]; ring
          have h3 : (0:ℝ) ≤ (1/2:ℝ)^L := pow_nonneg (by norm_num) L
          linarith
    have h4 : (0:ℝ) ≤ 2*(1/2:ℝ)^L := by positivity
    linarith [hmain L]
  have hnonneg : ∀ n : ℕ, (0:ℝ) ≤ (if ¬ n.Prime then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0) := by
    intro n; split_ifs <;> positivity
  have hpt : ∀ n : ℕ, K ≤ n →
      (if ¬ n.Prime then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0)
        ≤ g n * (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
    intro n hnK
    by_cases hnp : n.Prime
    · simp [hnp]
    · rw [if_pos hnp, if_pos hnp]
      rw [npe_coeff_norm, mul_pow]
      have ht0 : (0:ℝ) ≤ (n:ℝ)/x := by positivity
      have ht2n : (2:ℝ) ≤ (n:ℝ)/x := ht2 n hnK
      have hgn : (0:ℝ) ≤ (n:ℝ)/x := ht0
      have hΛ : (0:ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
        ArithmeticFunction.vonMangoldt_nonneg
      have hsq := npe_mangoldt_sq n hnp
      -- the log comparison
      have hlog : Real.log (n:ℝ) ≤ ((n:ℝ)/x) * Real.log x := by
        have hnpos : (0:ℝ) < (n:ℝ) := by
          have : (1:ℝ) ≤ (n:ℝ) := by
            have h1 : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnK
            linarith
          linarith
        have hnge : x ≤ (n:ℝ) := by
          have h1 : (K:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnK
          linarith
        have ht1 : (1:ℝ) ≤ (n:ℝ)/x := le_trans (by norm_num) ht2n
        have ht0' : (0:ℝ) < (n:ℝ)/x := by linarith
        have hsplit : Real.log (n:ℝ) = Real.log x + Real.log ((n:ℝ)/x) := by
          nth_rewrite 1 [show (n:ℝ) = x * ((n:ℝ)/x) by field_simp]
          exact Real.log_mul (ne_of_gt hx0) (ne_of_gt ht0')
        have hlogt : Real.log ((n:ℝ)/x) ≤ (n:ℝ)/x - 1 := Real.log_le_sub_one_of_pos ht0'
        rw [hsplit]
        nlinarith [hlogt, hlogx1, ht1]
      -- the weight bound
      have hgauss := Task420.etaPlus_gaussian_bound ht0
      have hη0 : (0:ℝ) ≤ |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)| := abs_nonneg _
      have hX : (0:ℝ) ≤ C1 * ((n:ℝ)/x) * Real.exp (-(((n:ℝ)/x)^2)/2) := by positivity
      have hE2 : Real.exp (-(((n:ℝ)/x)^2)/2)^2 = Real.exp (-(((n:ℝ)/x)^2)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hηsq : |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)|^2
          ≤ C1^2 * ((n:ℝ)/x)^2 * Real.exp (-(((n:ℝ)/x)^2)) := by
        have h1 : |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)|^2
            ≤ (C1 * ((n:ℝ)/x) * Real.exp (-(((n:ℝ)/x)^2)/2))^2 := by
          nlinarith [hgauss, hη0, hX]
        rw [show (C1 * ((n:ℝ)/x) * Real.exp (-(((n:ℝ)/x)^2)/2))^2
            = C1^2 * ((n:ℝ)/x)^2 * Real.exp (-(((n:ℝ)/x)^2)) by
          rw [mul_pow, mul_pow, hE2]] at h1
        exact h1
      have hlogxnn : (0:ℝ) ≤ Real.log x := hlogx0
      calc (ArithmeticFunction.vonMangoldt n : ℝ)^2
              * |LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x)|^2
          ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (n:ℝ) / 2)
              * (C1^2 * ((n:ℝ)/x)^2 * Real.exp (-(((n:ℝ)/x)^2))) :=
            mul_le_mul hsq hηsq (by positivity) (by positivity)
        _ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * (((n:ℝ)/x) * Real.log x) / 2)
              * (C1^2 * ((n:ℝ)/x)^2 * Real.exp (-(((n:ℝ)/x)^2))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith [hlog, hΛ, ht0, hlogxnn]
        _ = g n * (ArithmeticFunction.vonMangoldt n : ℝ) := by rw [hg]; ring
  have hband : ∀ L : ℕ, (∑ n ∈ Finset.Ico K (K * 2^L),
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      ≤ 1.77 * (∑ j ∈ Finset.range L, (1/2:ℝ)^j) * Real.sqrt (K:ℝ) * g K := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
        have hpw : K * 2^(L+1) = 2 * (K * 2^L) := by ring
        have hM0 : K ≤ K * 2^L := Nat.le_mul_of_pos_right K (pow_pos (by norm_num) L)
        have hM1 : K * 2^L ≤ K * 2^(L+1) := by rw [hpw]; omega
        have hAB : Finset.Ico K (K * 2^(L+1))
            = Finset.Ico K (K * 2^L) ∪ Finset.Ico (K * 2^L) (K * 2^(L+1)) :=
          (Finset.Ico_union_Ico_eq_Ico hM0 hM1).symm
        have hnew : (∑ n ∈ Finset.Ico (K * 2^L) (K * 2^(L+1)),
            (if ¬ n.Prime then
              ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
            ≤ 1.77 * (1/2:ℝ)^L * Real.sqrt (K:ℝ) * g K := by
          have hstep1 : (∑ n ∈ Finset.Ico (K * 2^L) (K * 2^(L+1)),
              (if ¬ n.Prime then
                ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
              ≤ ∑ n ∈ Finset.Ico (K * 2^L) (K * 2^(L+1)),
                  g (K * 2^L) * (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
            apply Finset.sum_le_sum
            intro n hn
            have hmem := Finset.mem_Ico.mp hn
            have hnK : K ≤ n := le_trans hM0 hmem.1
            have h1 := hpt n hnK
            have h2 : g n ≤ g (K * 2^L) := hganti hM0 hmem.1
            have hX : (0:ℝ) ≤ (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0) := by
              split_ifs <;> positivity
            exact h1.trans (mul_le_mul_of_nonneg_right h2 hX)
          have hstep2 : (∑ n ∈ Finset.Ico (K * 2^L) (K * 2^(L+1)),
                  g (K * 2^L) * (if ¬ n.Prime then (ArithmeticFunction.vonMangoldt n : ℝ) else 0))
              ≤ g (K * 2^L) * (1.251 * Real.sqrt ((K * 2^(L+1) : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (hgnn _)
            have hsub : Finset.Ico (K * 2^L) (K * 2^(L+1)) ⊆ Finset.range (K * 2^(L+1) + 1) := by
              intro n hn
              rw [Finset.mem_Ico] at hn
              rw [Finset.mem_range]
              omega
            have h1 := Finset.sum_le_sum_of_subset_of_nonneg
              (f := fun i : ℕ => (if ¬ i.Prime then (ArithmeticFunction.vonMangoldt i : ℝ) else 0))
              hsub (fun i _ _ => by split_ifs <;> positivity)
            have h2 : (10:ℝ)^8 ≤ ((K * 2^(L+1) : ℕ) : ℝ) := by
              have h3 : (K:ℝ) ≤ ((K * 2^(L+1) : ℕ) : ℝ) := by
                push_cast
                have : (K:ℝ) * 1 ≤ (K:ℝ) * 2^(L+1) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact one_le_pow₀ (by norm_num)
                simpa using this
              linarith
            exact h1.trans (npe_mass_le (K * 2^(L+1)) h2)
          have hstep3 : g (K * 2^L) * (1.251 * Real.sqrt ((K * 2^(L+1) : ℕ) : ℝ))
              ≤ 1.77 * (1/2:ℝ)^L * Real.sqrt (K:ℝ) * g K := by
            have hit := hgiter L
            have hgnnK : (0:ℝ) ≤ g K := hgnn K
            have hsqrt : Real.sqrt ((K * 2^(L+1) : ℕ) : ℝ) ≤ Real.sqrt 2 * 2^L * Real.sqrt (K:ℝ) := by
              have hc : ((K * 2^(L+1) : ℕ) : ℝ) = 2 * (2:ℝ)^L * (K:ℝ) := by push_cast; ring
              rw [hc]
              have hsm : Real.sqrt (2 * (2:ℝ)^L * (K:ℝ))
                  = Real.sqrt (2 * (2:ℝ)^L) * Real.sqrt (K:ℝ) :=
                Real.sqrt_mul (by positivity) (K:ℝ)
              rw [hsm]
              have hle : Real.sqrt (2 * (2:ℝ)^L) ≤ Real.sqrt 2 * 2^L := by
                have hp : (2:ℝ) * 2^L ≤ (Real.sqrt 2 * 2^L)^2 := by
                  rw [mul_pow, Real.sq_sqrt (by norm_num)]
                  have h4 : (1:ℝ) ≤ (2:ℝ)^L := one_le_pow₀ (by norm_num)
                  nlinarith
                calc Real.sqrt (2 * (2:ℝ)^L) ≤ Real.sqrt ((Real.sqrt 2 * 2^L)^2) :=
                      Real.sqrt_le_sqrt hp
                  _ = Real.sqrt 2 * 2^L := Real.sqrt_sq (by positivity)
              have hs0 : (0:ℝ) ≤ Real.sqrt (K:ℝ) := Real.sqrt_nonneg _
              exact mul_le_mul_of_nonneg_right hle hs0
            have hs0 : (0:ℝ) ≤ Real.sqrt (K:ℝ) := Real.sqrt_nonneg _
            have hs2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
            have h4 : (0:ℝ) ≤ (1/4:ℝ)^L := by positivity
            have h5 : (0:ℝ) ≤ (2:ℝ)^L := by positivity
            have h3 : (1/4:ℝ)^L * (2:ℝ)^L = (1/2:ℝ)^L := by
              rw [← mul_pow]; norm_num
            have h6 : Real.sqrt 2 ≤ 1.4143 := by
              rw [Real.sqrt_le_iff]; constructor <;> norm_num
            have h7 : 1.251 * Real.sqrt 2 ≤ 1.77 := by nlinarith [h6]
            have hp1 : (0:ℝ) ≤ (1/2:ℝ)^L := by positivity
            calc g (K * 2^L) * (1.251 * Real.sqrt ((K * 2^(L+1) : ℕ) : ℝ))
                ≤ ((1/4:ℝ)^L * g K) * (1.251 * (Real.sqrt 2 * 2^L * Real.sqrt (K:ℝ))) := by
                  apply mul_le_mul hit _ (by positivity) (by positivity)
                  exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
              _ = 1.251 * Real.sqrt 2 * ((1/4:ℝ)^L * 2^L) * Real.sqrt (K:ℝ) * g K := by ring
              _ = 1.251 * Real.sqrt 2 * (1/2:ℝ)^L * Real.sqrt (K:ℝ) * g K := by rw [h3]
              _ ≤ 1.77 * (1/2:ℝ)^L * Real.sqrt (K:ℝ) * g K := by
                  have hs0' : (0:ℝ) ≤ Real.sqrt (K:ℝ) := hs0
                  have hgnnK' : (0:ℝ) ≤ g K := hgnnK
                  apply mul_le_mul_of_nonneg_right _ hgnnK'
                  apply mul_le_mul_of_nonneg_right _ hs0'
                  exact mul_le_mul_of_nonneg_right h7 hp1
          exact hstep1.trans (hstep2.trans hstep3)
        rw [hAB, Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive K (K * 2^L) (K * 2^(L+1)))]
        rw [Finset.sum_range_succ]
        nlinarith [ih, hnew]
  have hrN : (∑ n ∈ Finset.Ico K N,
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      ≤ 1.77 * 2 * Real.sqrt (K:ℝ) * g K := by
    have hsub : Finset.Ico K N ⊆ Finset.Ico K (K * 2^N) := by
      intro n hn
      rw [Finset.mem_Ico] at hn ⊢
      refine ⟨hn.1, ?_⟩
      have h1 : N < 2^N := Nat.lt_two_pow_self
      have h2 : 2^N ≤ K * 2^N := Nat.le_mul_of_pos_left (2^N) (by omega)
      omega
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
    have hb := hband N
    have hg2 : (∑ j ∈ Finset.range N, (1/2:ℝ)^j) ≤ 2 := hgeom N
    have hs0 : (0:ℝ) ≤ Real.sqrt (K:ℝ) := Real.sqrt_nonneg _
    have hgnnK := hgnn K
    calc _ ≤ 1.77 * (∑ j ∈ Finset.range N, (1/2:ℝ)^j) * Real.sqrt (K:ℝ) * g K :=
          hmono.trans hb
      _ ≤ 1.77 * 2 * Real.sqrt (K:ℝ) * g K := by
          have hc : (0:ℝ) ≤ 1.77 * Real.sqrt (K:ℝ) * g K :=
            mul_nonneg (mul_nonneg (by norm_num) hs0) hgnnK
          calc 1.77 * (∑ j ∈ Finset.range N, (1/2:ℝ)^j) * Real.sqrt (K:ℝ) * g K
              = (1.77 * Real.sqrt (K:ℝ) * g K) * (∑ j ∈ Finset.range N, (1/2:ℝ)^j) := by ring
            _ ≤ (1.77 * Real.sqrt (K:ℝ) * g K) * 2 := mul_le_mul_of_nonneg_left hg2 hc
            _ = 1.77 * 2 * Real.sqrt (K:ℝ) * g K := by ring
  have hsqK : Real.sqrt (K:ℝ) ≤ 2.7 * Real.sqrt x := by
    have h1 : Real.sqrt (K:ℝ) ≤ Real.sqrt (7*x) := Real.sqrt_le_sqrt hKle
    have h2 : Real.sqrt (7*x) = Real.sqrt 7 * Real.sqrt x := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 7)]
    have h3 : Real.sqrt 7 ≤ 2.7 := by
      rw [Real.sqrt_le_iff]; constructor <;> norm_num
    rw [h2] at h1
    nlinarith [Real.sqrt_nonneg x]
  have hgK : g K ≤ Real.log x * C1^2 / 2 * (216 * Real.exp (-36)) := by
    rw [hg]
    have h6 : (6:ℝ) ≤ (K:ℝ)/x := by rw [le_div_iff₀ hx0]; linarith
    have hcube := npe_cube_exp_anti (v := 6) (u := (K:ℝ)/x) (by norm_num) h6
    have hc : (6:ℝ)^3 * Real.exp (-((6:ℝ)^2)) = 216 * Real.exp (-36) := by norm_num
    rw [hc] at hcube
    exact mul_le_mul_of_nonneg_left hcube (by positivity)
  have he36 : Real.exp (-36) ≤ 3e-16 := by
    have h1 : Real.exp (36:ℝ) = (Real.exp 1)^36 := by
      rw [show (36:ℝ) = ((36:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h2 : (4.0e15:ℝ) ≤ Real.exp 36 := by
      rw [h1]
      have h3 : (4.0e15:ℝ) ≤ (2.7182818283:ℝ)^36 := by norm_num
      have h4 : (2.7182818283:ℝ)^36 ≤ (Real.exp 1)^36 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 36
      linarith
    have h5 : Real.exp (-36) = 1 / Real.exp 36 := by
      rw [eq_div_iff (ne_of_gt (Real.exp_pos 36)), ← Real.exp_add]
      norm_num
    rw [h5, div_le_iff₀ (Real.exp_pos 36)]
    nlinarith [h2]
  have hcomb : Real.log x * C1^2 / 2 * (216 * Real.exp (-36))
      ≤ Real.log x * 1.348e8 / 2 * (216 * 3e-16) := by
    have h1 : Real.log x * C1^2 / 2 ≤ Real.log x * 1.348e8 / 2 := by nlinarith [hC1sq, hlogx0]
    have h2 : (0:ℝ) ≤ Real.log x * 1.348e8 / 2 := by positivity
    have h3 : 216 * Real.exp (-36) ≤ 216 * 3e-16 := by nlinarith [he36]
    exact mul_le_mul h1 h3 (by positivity) h2
  have hsq0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc (∑ n ∈ Finset.Ico (Nat.ceil (6*x) + 1) N,
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
      = (∑ n ∈ Finset.Ico K N,
        (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0)) := by rw [hK]
    _ ≤ 1.77 * 2 * Real.sqrt (K:ℝ) * g K := hrN
    _ ≤ 3.6 * (2.7 * Real.sqrt x) *
          (Real.log x * 1.348e8 / 2 * (216 * 3e-16)) := by
        have hg' : g K ≤ Real.log x * 1.348e8 / 2 * (216 * 3e-16) := hgK.trans hcomb
        have h1 : 1.77 * 2 * Real.sqrt (K:ℝ) ≤ 3.6 * (2.7 * Real.sqrt x) := by
          nlinarith [hsqK, hsq0]
        exact mul_le_mul h1 hg' (hgnn K) (by positivity)
    _ ≤ 0.0001 * Real.log x * Real.sqrt x := by
        have hp : (0:ℝ) ≤ Real.log x * Real.sqrt x := mul_nonneg hlogx0 hsq0
        nlinarith [hp]

set_option maxHeartbeats 2000000 in
/-- LEAF. The nonprime indices have the stated coefficient square budget.
Helfgott v2 page 51 nonprime power estimate and book page 267 bounds for
C eta plus zero and one, combined on page 268 equation 14.28.
This excludes all prime indices and has no small prime contribution. -/
theorem nonprime_coeff_square_upper (x : ℝ) (hx : 4.9e26 ≤ x) :
    (∑' n : ℕ, if ¬n.Prime then
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ ^ 2 else 0) ≤
      (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hlogx1 : (1:ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) he
  have hlogx0 : (0:ℝ) ≤ Real.log x := le_trans (by norm_num) hlogx1
  have hs0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlog7 : Real.log (7*x) ≤ Real.log x + 2 := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
    have he2 : (7:ℝ) ≤ Real.exp 2 := by
      have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [h1]
      nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
    have h2 : Real.log 7 ≤ 2 := (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 7)).mpr he2
    linarith
  have hfin : 2 * Real.log (7*x) * Real.sqrt x + 0.0001 * Real.log x * Real.sqrt x
      ≤ (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x := by
    have h1 : 2 * Real.log (7*x) * Real.sqrt x ≤ 2 * (Real.log x + 2) * Real.sqrt x := by
      apply mul_le_mul_of_nonneg_right _ hs0
      linarith
    have hp : (0:ℝ) ≤ Real.log x * Real.sqrt x := mul_nonneg hlogx0 hs0
    nlinarith [h1, hp, hlogx0, hs0]
  have hkey : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      (if ¬ n.Prime then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0)) ≤
      (2.33744 * (2 + Real.log x) + 0.44937) * Real.sqrt x := by
    intro N
    by_cases hNK : N ≤ Nat.ceil (6*x) + 1
    · have hsub : Finset.range N ⊆ Finset.range (Nat.ceil (6*x) + 1) :=
        Finset.range_subset_range.mpr hNK
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun n : ℕ => (if ¬ n.Prime then
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0))
        hsub (fun i _ _ => by split_ifs <;> positivity)
      have h2 := npe_part1 x hx
      have h3 : (0:ℝ) ≤ 0.0001 * Real.log x * Real.sqrt x := by positivity
      linarith [h1, h2, hfin, h3]
    · push_neg at hNK
      have h1 := npe_part1 x hx
      have h2 := npe_tail x hx N
      rw [← Finset.sum_range_add_sum_Ico (fun n : ℕ => (if ¬ n.Prime then
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (LeanLab.HelfgottArcs.etaPlus ((n:ℝ)/x) : ℂ)‖ ^ 2 else 0)) hNK.le]
      linarith [h1, h2, hfin]
  refine Real.tsum_le_of_sum_range_le ?_ ?_
  · intro n
    split_ifs <;> positivity
  · exact hkey


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
