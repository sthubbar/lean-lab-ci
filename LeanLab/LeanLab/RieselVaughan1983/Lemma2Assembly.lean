import LeanLab.RieselVaughan1983.Lemma2LogMoments
import LeanLab.RieselVaughan1983.Lemma2Summatory

/-! Equation 3.8 and a conditional assembly of Lemma 2 on pages 50 and 51.
AI wrote the Lean code. Binary Goldbach is OPEN.
The two evaluated logarithmic moments are explicit unproved inputs. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real
noncomputable section

def mainCoefficient (y : ℝ) : ℝ :=
  Real.log y ^ 2 / 2 + 2 * eulerMascheroniConstant * Real.log y +
    eulerMascheroniConstant ^ 2 - 2 * stieltjes1

def mainKernel (y : ℝ) (n : ℕ) : ℝ :=
  mainCoefficient y * g n - (Real.log y + 2 * eulerMascheroniConstant) *
    (g n * Real.log n) + (g n * Real.log n ^ 2) / 2

/-- Page 51 first evaluated moment, with the sign from differentiating n^-w. -/
def FirstMomentP : Prop := moment 1 = -(A1 / Ctw)

/-- Page 51 second evaluated moment. -/
def SecondMomentP : Prop := moment 2 = (Real.log 2 ^ 2 / 4 - A2 + A1 ^ 2) / Ctw

lemma error_summable_norm (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖g n * lem1E stieltjes1 (y / n)‖) := by
  apply (mass_summable.mul_left (1641 / 1000 * y ^ (-(1 / 3 : ℝ)))).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  simpa only [Real.norm_eq_abs, mass] using
    error_term_bound (fun n => g n) (by simp) y hy n

lemma divisor_main_error (y : ℝ) (hy : 0 < y) (n : ℕ) :
    g n * divisorPartial (y / n) =
      mainKernel y n + g n * lem1E stieltjes1 (y / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mainKernel]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold mainKernel mainCoefficient lem1E divisorPartial
    rw [Real.log_div hy.ne' hn0]
    ring

lemma mainKernel_hasSum (y : ℝ) :
    HasSum (mainKernel y)
      (mainCoefficient y / Ctw - (Real.log y + 2 * eulerMascheroniConstant) *
        moment 1 + moment 2 / 2) := by
  have h0 : HasSum (fun n : ℕ => g n) (1 / Ctw) := by
    have he : (∑' n : ℕ, g n) = 1 / Ctw := by simpa [G] using G_zero
    rw [← he]
    exact g_summable_norm.of_norm.hasSum
  have h := ((h0.mul_left (mainCoefficient y)).sub
    (moment_one_hasSum.mul_left (Real.log y + 2 * eulerMascheroniConstant))).add
      (moment_two_hasSum.div_const 2)
  change HasSum (fun n : ℕ => mainCoefficient y * g n -
    (Real.log y + 2 * eulerMascheroniConstant) * (g n * Real.log n) +
      (g n * Real.log n ^ 2) / 2) _
  simpa only [mul_one_div] using h

/-- Equation 3.8, with the two logarithmic moments unevaluated. -/
theorem eq38 (y : ℝ) (hy : 1 ≤ y) :
    S y = mainCoefficient y / Ctw -
      (Real.log y + 2 * eulerMascheroniConstant) * moment 1 + moment 2 / 2 +
        ∑' n : ℕ, g n * lem1E stieltjes1 (y / n) := by
  have hy0 : 0 < y := by linarith
  rw [eq35 y hy]
  have h := (mainKernel_hasSum y).add (error_summable_norm y hy0).of_norm.hasSum
  have he : (fun n : ℕ => g n * divisorPartial (y / n)) =
      (fun n => mainKernel y n + g n * lem1E stieltjes1 (y / n)) :=
    funext (divisor_main_error y hy0)
  rw [he]
  exact h.tsum_eq

/-- Lemma 2, CONDITIONAL ON the two evaluated logarithmic moments. -/
theorem lemma2_of_moments (h1 : FirstMomentP) (h2 : SecondMomentP) : Lemma2P := by
  intro y hy
  have hy0 : 0 < y := by linarith
  have hS := eq38 y hy
  rw [FirstMomentP] at h1
  rw [SecondMomentP] at h2
  rw [h1, h2] at hS
  have hmain := main_term_identity Ctw A1 A2 eulerMascheroniConstant stieltjes1
    (Real.log y) Ctw_pos.ne'
  have he : 2 * Ctw * S y - Real.log y ^ 2 - A3 * Real.log y - A4 =
      (2 * Ctw) * (∑' n : ℕ, g n * lem1E stieltjes1 (y / n)) := by
    rw [hS]
    simp only [mainCoefficient, A4, A3]
    nlinarith [hmain]
  rw [he, abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Ctw_pos)]
  have h := mul_lt_mul_of_pos_left (eq37 y hy0) (mul_pos (by norm_num : (0 : ℝ) < 2) Ctw_pos)
  unfold A5
  nlinarith

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.error_summable_norm
#print axioms LeanLab.RieselVaughan1983.Lemma2.divisor_main_error
#print axioms LeanLab.RieselVaughan1983.Lemma2.mainKernel_hasSum
#print axioms LeanLab.RieselVaughan1983.Lemma2.eq38
#print axioms LeanLab.RieselVaughan1983.Lemma2.lemma2_of_moments
