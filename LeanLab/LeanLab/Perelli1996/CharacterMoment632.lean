/-
Perelli 1996, page 485 equation 24.
Finite character Parseval and the uniform full period energy bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Character632
import LeanLab.Perelli1996.Parseval103
namespace LeanLab.Perelli1996.Decomp88
open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
/-- Page 485 equation 24. Finite Parseval bounds every character energy by
 twice the prime second moment and twice the inclusive geometric coefficient count. -/
theorem character_full_period_bound (M q : ℕ) (χ : DirichletCharacter ℂ q)
    (δ : ℂ) (hδ : ‖δ‖ ≤ 1) :
    (∫ η in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
        δ * Kernel.T 0 (M + 1) η‖ ^ 2) ≤
      2 * (∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum M α‖ ^ 2) + 2 * (M + 1) := by
  have hid :
      (∫ η in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖(∑ n ∈ range (M + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          δ * Kernel.T 0 (M + 1) η‖ ^ 2) =
      ∑ n ∈ range (M + 1), ‖(Λ n : ℂ) * χ n - δ‖ ^ 2 := by
    have h := LeanLab.PNTPort.Gallagher.parseval
      (fun n => (Λ n : ℂ) * χ n - δ) (M + 1)
    simpa only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
      Kernel.T, Nat.zero_add, LeanLab.PNTPort.LargeSieve.e, Kernel.e] using h
  rw [hid]
  unfold primeSum
  rw [Parseval103.integral_norm_sum_sq]
  calc
    _ ≤ ∑ n ∈ range (M + 1), (2 * (Λ n) ^ 2 + 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      have hχ : ‖(Λ n : ℂ) * χ n‖ ≤ Λ n := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛ]
        exact mul_le_of_le_one_right hΛ (DirichletCharacter.norm_le_one _ _)
      have hnrm : ‖(Λ n : ℂ) * χ n - δ‖ ≤ Λ n + 1 :=
        (norm_sub_le _ _).trans (add_le_add hχ hδ)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hnrm 2
      nlinarith [sq_nonneg (Λ n - 1)]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
      ring

/-- Page 485 equation 24. The full period character energy has uniform N log N scale.
This proves the Parseval input used to discard bad characters. -/
theorem character_full_period_scaled (c : ℝ) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℂ, ‖δ‖ ≤ 1 →
      (∫ η in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖(∑ n ∈ range (⌊c * N⌋₊ + 1), (Λ n : ℂ) * χ n * Kernel.e ((n : ℝ) * η)) -
          δ * Kernel.T 0 (⌊c * N⌋₊ + 1) η‖ ^ 2) ≤ C * N * Real.log N := by
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := Parseval103.prime_second_moment_scaled c hc
  refine ⟨2 * CP + 2 * (c + 1), max NP (Real.exp 1), by positivity,
    hNP.trans (le_max_left _ _), ?_⟩
  intro N hN q χ δ hδ
  have hN3 : 3 ≤ N := hNP.trans ((le_max_left _ _).trans hN)
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
  have hcount : (⌊c * N⌋₊ : ℝ) + 1 ≤ (c + 1) * N := by
    have hfl := Nat.floor_le (by positivity : 0 ≤ c * N)
    nlinarith
  have henergy := character_full_period_bound ⌊c * N⌋₊ q χ δ hδ
  have hprime := hp N ((le_max_left _ _).trans hN)
  have hsave := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 2 * (c + 1) * N by positivity)
  nlinarith
end LeanLab.Perelli1996.Decomp88
