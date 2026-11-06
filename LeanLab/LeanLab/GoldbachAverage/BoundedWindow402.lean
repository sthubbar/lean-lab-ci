import LeanLab.GoldbachAverage.Decomp287d

/-!
The bounded window extension in Decomp287d, from BHMS arXiv 1704.06103v2 page 17
 to P0051 page 20 eq. 84. The extension is an elementary derived bound.
A window of length at most two contains at most two integer indices.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.BoundedWindow402
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

/-- The psi increment is its finite window sum, in the BHMS page 17 explicit formula context. -/
theorem psi_increment_sum {t h : ℝ} (hh : 0 ≤ h) :
    Chebyshev.psi (t + h) - Chebyshev.psi t =
      ∑ n ∈ Ioc ⌊t⌋₊ ⌊t + h⌋₊, Λ n := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  have hlo : ⌊t⌋₊ ≤ ⌊t + h⌋₊ := Nat.floor_mono (by linarith : t ≤ t + h)
  have hs := sum_Ico_eq_sub (fun n : ℕ => (Λ n : ℝ)) (Nat.succ_le_succ hlo)
  have hsets : Ico (⌊t⌋₊ + 1) (⌊t + h⌋₊ + 1) = Ioc ⌊t⌋₊ ⌊t + h⌋₊ := by
    ext n
    simp only [mem_Ico, mem_Ioc]
    omega
  rw [hsets] at hs
  simpa only [← Nat.range_succ_eq_Icc_zero] using hs.symm

/-- A length two window contains at most two terms, the bounded window step after BHMS page 17. -/
theorem short_window_card {t h : ℝ} (ht : 0 ≤ t) (hh : h ≤ 2) :
    (Ioc ⌊t⌋₊ ⌊t + h⌋₊).card ≤ 2 := by
  have hf := Nat.floor_mono (show t + h ≤ t + (2 : ℕ) by norm_num; linarith)
  rw [Nat.floor_add_natCast ht] at hf
  rw [Nat.card_Ioc]
  omega

/-- The logarithmic pointwise bound for the derived bounded window extension of BHMS page 17. -/
theorem short_psi_increment {x t h : ℝ} (hx : 2 ≤ x) (ht : t ∈ Set.Icc x (2 * x))
    (hh : 0 ≤ h) (hh2 : h ≤ 2) :
    Chebyshev.psi (t + h) - Chebyshev.psi t ≤ 6 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hcoeff : ∀ n ∈ Ioc ⌊t⌋₊ ⌊t + h⌋₊, (Λ n : ℝ) ≤ 3 * Real.log x := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (mem_Ioc.mp hn).1; omega)
    have hnu : (n : ℝ) ≤ t + h :=
      (by exact_mod_cast (mem_Ioc.mp hn).2 : (n : ℝ) ≤ ⌊t + h⌋₊).trans
        (Nat.floor_le (by linarith))
    have hnx : (n : ℝ) ≤ x ^ 3 := by
      have hsq : 3 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 2)]
      have hxx : 3 * x ≤ x ^ 3 := by
        have hm := mul_le_mul_of_nonneg_left hsq hx0.le
        nlinarith only [hm]
      linarith [ht.2]
    calc (Λ n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (x ^ 3) := Real.log_le_log hn0 hnx
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  rw [psi_increment_sum hh]
  calc _ ≤ ∑ n ∈ Ioc ⌊t⌋₊ ⌊t + h⌋₊, 3 * Real.log x := sum_le_sum hcoeff
    _ = ((Ioc ⌊t⌋₊ ⌊t + h⌋₊).card : ℝ) * (3 * Real.log x) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * (3 * Real.log x) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast short_window_card ht0 hh2) (by positivity)
    _ = _ := by ring

/-- The integrand bound in the bounded window extension of BHMS page 17. -/
theorem short_error_square {x t h : ℝ} (hx : 2 ≤ x) (ht : t ∈ Set.Icc x (2 * x))
    (hh : 0 ≤ h) (hh2 : h ≤ 2) :
    (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 ≤ 144 * Real.log x ^ 4 := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hu := short_psi_increment hx ht hh hh2
  have hl := Chebyshev.psi_mono (show t ≤ t + h by linarith)
  have habs : |Chebyshev.psi (t + h) - Chebyshev.psi t - h| ≤ 6 * Real.log x := by
    rw [abs_le]
    constructor <;> linarith
  have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hs
  have hl2 : (1 : ℝ) / 4 ≤ Real.log x ^ 2 := by nlinarith [sq_nonneg (Real.log x - 1 / 2)]
  have hm := mul_le_mul_of_nonneg_right hl2 (sq_nonneg (Real.log x))
  nlinarith

/-- The exact bounded_window_variance leaf is proved with the explicit constant 144.
This is a derived elementary extension, not a printed BHMS constant. -/
theorem bounded_window_variance_proved : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 1 ≤ h → h ≤ 2 →
      (∫ t in x..(2 * x), (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) ≤
        C * x * Real.log x ^ 4 := by
  refine ⟨144, by norm_num, ?_⟩
  intro x h hx hh hh2
  have hfull := Decomp82.short_error_integrable (by linarith : (0 : ℝ) ≤ 2 * x)
    (by linarith : 0 ≤ h)
  have hi := hfull.mono_set (show Set.uIcc x (2 * x) ⊆ Set.uIcc 0 (2 * x) by
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x), Set.uIcc_of_le (by linarith : 0 ≤ 2 * x)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  have hb := intervalIntegral.integral_mono_on (by linarith : x ≤ 2 * x) hi
    (intervalIntegrable_const (c := 144 * Real.log x ^ 4))
    (fun t ht => short_error_square hx ht (by linarith) hh2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  nlinarith only [hb]

example : type_of% Decomp287d.bounded_window_variance = type_of% bounded_window_variance_proved := rfl

end LeanLab.GoldbachAverage.BoundedWindow402
