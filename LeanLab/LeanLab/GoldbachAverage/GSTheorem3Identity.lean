import LeanLab.GoldbachAverage.EGSInvariant

/-!
P0051, arXiv 2110.14250v2, Theorem 3 eq. 20 page 4.
The circle integral extracts the partial sum of Lambda minus one.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage
open Finset Complex
open scoped ArithmeticFunction.vonMangoldt

lemma summable_cf {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ‖cf n‖ * r ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_right (norm_cf_le n) (by positivity))
    (summable_geom_poly hr0 hr1)

/-- The linear coefficient extraction identity. -/
theorem psi_error_integral_coefficients (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    (∫ α in (0 : ℝ)..1, (PsiGen r α - IGen r α) * IGenN N (1 / r) (-α)) = ∑ m ∈ Icc 1 N, cf m := by
  set D : ℕ → ℝ → ℂ := fun n α => cf n * (r : ℂ) ^ n * eAdd (α * n) with hD
  set H : ℕ → ℝ → ℂ := fun m α => ((1 / r : ℝ) : ℂ) ^ m * eAdd (-α * m) with hH
  have hpt : ∀ α : ℝ, (PsiGen r α - IGen r α) * IGenN N (1 / r) (-α) =
      ∑ m ∈ Icc 1 N, ∑' n, D n α * H m α := by
    intro α
    rw [psi_sub_I hr0.le hr, IGenN, mul_sum]
    apply sum_congr rfl; intro m _
    rw [← tsum_mul_right]
    rfl
  have hDb : ∀ n α, ‖D n α‖ = ‖cf n‖ * r ^ n := by
    intro n α
    simp only [hD, norm_mul, norm_pow, norm_eAdd, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0.le, mul_one]
  have hHb : ∀ m α, ‖H m α‖ = (1 / r) ^ m := by
    intro m α
    simp only [hH, norm_mul, norm_pow, norm_eAdd, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / r), mul_one]
  have hcont : ∀ n m, Continuous fun α => D n α * H m α := by
    intro n m
    simp only [hD, hH]
    have h1 := continuous_eAdd_mul (n : ℝ)
    have h2 : Continuous fun α : ℝ => eAdd (-α * m) := by unfold eAdd; fun_prop
    exact ((continuous_const.mul h1)).mul (continuous_const.mul h2)
  have hsum : ∀ m, Summable (fun n => ‖cf n‖ * r ^ n * (1 / r) ^ m) :=
    fun m => (summable_cf hr0.le hr).mul_right _
  have hbound : ∀ m n α, ‖D n α * H m α‖ ≤ ‖cf n‖ * r ^ n * (1 / r) ^ m := by
    intro m n α; rw [norm_mul, hDb, hHb]
  have hcm : ∀ m, Continuous fun α => ∑' n, D n α * H m α := fun m =>
    continuous_tsum (fun n => hcont n m) (hsum m) (fun n α => hbound m n α)
  simp_rw [hpt]
  rw [intervalIntegral.integral_finset_sum (fun m _ => (hcm m).intervalIntegrable _ _)]
  apply sum_congr rfl; intro m _
  have hhs := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := 1)
    (μ := MeasureTheory.volume) (F := fun n α => D n α * H m α)
    (fun n _ => ‖cf n‖ * r ^ n * (1 / r) ^ m)
    (fun n => (hcont n m).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun α _ => hbound m n α)
    (Filter.Eventually.of_forall fun α _ => hsum m)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun α _ =>
      (Summable.of_norm_bounded (hsum m) (fun n => hbound m n α)).hasSum)
  rw [← hhs.tsum_eq]
  have hval : ∀ n, ∫ α in (0 : ℝ)..1, D n α * H m α = if n = m then cf m else 0 := by
    intro n
    have e : ∀ α : ℝ, D n α * H m α =
        (cf n * (r : ℂ) ^ n * ((1 / r : ℝ) : ℂ) ^ m) * eAdd (α * ((n : ℤ) - m : ℤ)) := by
      intro α
      simp only [hD, hH]
      have : eAdd (α * n) * eAdd (-α * m) = eAdd (α * ((n : ℤ) - m : ℤ)) := by
        rw [← eAdd_add]; congr 1; push_cast; ring
      rw [← this]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_eAdd]
    split_ifs with h1 h2 h2
    · subst h2
      rw [mul_one, mul_assoc, ← mul_pow]
      push_cast
      rw [mul_one_div_cancel (by exact_mod_cast hr0.ne'), one_pow, mul_one]
    · exfalso; apply h2; omega
    · exfalso; apply h1; rw [h2]; simp
    · ring
  simp_rw [hval]
  rw [tsum_ite_eq]

/-- Theorem 3 eq. 20, for every admissible radius. -/
theorem gs_theorem3_identity (N : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((Chebyshev.psi N - N : ℝ) : ℂ) =
      ∫ α in (0 : ℝ)..1, (PsiGen r α - IGen r α) * IGenN N (1 / r) (-α) := by
  rw [psi_error_integral_coefficients N hr0 hr1]
  have he : ∀ m ∈ Icc 1 N, cf m = ((Λ m - 1 : ℝ) : ℂ) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    simp [cf, hm0]
  rw [sum_congr rfl he, ← Complex.ofReal_sum, sum_sub_distrib, sum_const, Nat.card_Icc]
  have hsum : ∑ m ∈ Icc 1 N, Λ m = Chebyshev.psi N := by
    have he : Icc 0 N = insert 0 (Icc 1 N) := by
      ext n
      simp only [mem_Icc, mem_insert]
      omega
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, he, sum_insert (by simp)]
    simp
  rw [hsum]
  congr 1
  simp

/-- Concrete admissible instance at N equals two and radius one half. -/
theorem gs_theorem3_at_two :
    ((Chebyshev.psi 2 - 2 : ℝ) : ℂ) =
      ∫ α in (0 : ℝ)..1, (PsiGen (1 / 2) α - IGen (1 / 2) α) * IGenN 2 2 (-α) := by
  convert gs_theorem3_identity 2 (r := 1 / 2) (by norm_num) (by norm_num) using 1 <;> norm_num

end LeanLab.GoldbachAverage
