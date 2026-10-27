import LeanLab.Ternary78.GammaTail

/-
AI wrote this Lean code. Binary Goldbach is open.
Elementary summability from finite height fibers, quadratic counts and quartic decay.
This file has no cited analytic input.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- A quadratic fiber bound and quartic weight decay imply real summability. -/
theorem summable_of_quadratic_fibers {ι : Type*} (b : ι → ℕ)
    [∀ n, Fintype {a // b a = n}] (w : ι → ℝ) (hw0 : ∀ a, 0 ≤ w a)
    {C G : ℝ} (hG : 0 ≤ G)
    (hcard : ∀ n : ℕ, (Fintype.card {a // b a = n} : ℝ) ≤ C * (n + 1 : ℝ) ^ 2)
    (hw : ∀ a, w a ≤ G / (b a + 1 : ℝ) ^ 4) : Summable w := by
  classical
  have hinner (n : ℕ) : (∑' a : {a // b a = n}, w a) ≤ C * G / (n + 1 : ℝ) ^ 2 := by
    rw [tsum_fintype]
    calc
      (∑ a : {a // b a = n}, w a) ≤ ∑ _a : {a // b a = n}, G / (n + 1 : ℝ) ^ 4 := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [a.property] using hw a.val
      _ = (Fintype.card {a // b a = n} : ℝ) * (G / (n + 1 : ℝ) ^ 4) := by simp
      _ ≤ (C * (n + 1 : ℝ) ^ 2) * (G / (n + 1 : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right (hcard n) (by positivity)
      _ = C * G / (n + 1 : ℝ) ^ 2 := by field_simp
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    summable_one_div_nat_pow.mpr (by norm_num)
  have hp' : Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have houter : Summable (fun n : ℕ => ∑' a : {a // b a = n}, w a) := by
    have hnn (n : ℕ) : 0 ≤ ∑' a : {a // b a = n}, w a :=
      tsum_nonneg (fun (a : {a // b a = n}) => hw0 a.val)
    have hbound : Summable (fun n : ℕ => C * G / (n + 1 : ℝ) ^ 2) := by
      simpa only [mul_one_div] using hp'.mul_left (C * G)
    exact Summable.of_nonneg_of_le hnn hinner hbound
  have hsigma : Summable (fun p : Σ n, {a // b a = n} => w p.2.val) :=
    (summable_sigma_of_nonneg (fun (p : Σ n, {a // b a = n}) => hw0 p.2.val)).mpr
      ⟨fun n => (hasSum_fintype (fun a : {a // b a = n} => w a.val)).summable, houter⟩
  exact (Equiv.sigmaFiberEquiv b).summable_iff.mp hsigma

#print axioms summable_of_quadratic_fibers

/-- The proved quartic Gamma tail supplies the weight hypothesis of the criterion. -/
theorem summable_gamma_of_quadratic_bins {ι : Type*} (γ : ι → ℝ) (b : ι → ℕ)
    [∀ n, Fintype {a // b a = n}] (hb : ∀ a, (b a : ℝ) ≤ |γ a|)
    {C σ : ℝ} (hσ : 0 < σ)
    (hcard : ∀ n : ℕ, (Fintype.card {a // b a = n} : ℝ) ≤ C * (n + 1 : ℝ) ^ 2) :
    Summable (fun a => ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * Complex.I)‖) := by
  let G : ℝ := 2 ^ (4 : ℕ) * max (Real.Gamma σ) (Real.Gamma (σ + 4))
  have hG : 0 ≤ G := by
    dsimp [G]
    exact mul_nonneg (by norm_num) ((Real.Gamma_pos_of_pos hσ).le.trans (le_max_left _ _))
  apply summable_of_quadratic_fibers b _ (fun _ => norm_nonneg _) hG hcard
  intro a
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (b a + 1 : ℝ) ^ 4)).mpr
  calc
    ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * Complex.I)‖ * (b a + 1 : ℝ) ^ 4 ≤
        ‖Complex.Gamma ((σ : ℂ) + (γ a : ℂ) * Complex.I)‖ * (1 + |γ a|) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity) (by linarith [hb a]) 4
    _ ≤ G := by
      simpa [G, mul_comm] using gamma_norm_mul_one_add_abs_pow_le hσ (γ a) 4

#print axioms summable_gamma_of_quadratic_bins

end LeanLab.Ternary78.Bennett
