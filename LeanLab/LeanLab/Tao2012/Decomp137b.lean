/-
Tao 2012, arXiv 1201.6656v4, page 17, Lemma 4.5.
CODEX task137, track T1. AI wrote this Lean code. Goldbach is open.
The cutoff hypotheses are those stated at the start of Section 4 on page 15.
-/
import LeanLab.Tao2012.Decomp1555a

namespace LeanLab.Tao2012.Decomp137b

open Real Finset MeasureTheory
open LeanLab.Tao2012.Decomp1555

/-- CITED. Tao 2012, page 17, Lemma 4.5, global L2 estimate.
The real part on the right is the real nonnegative sum at frequency zero. -/
def Lemma4_5 : Prop :=
  ∀ (η : ℝ → ℝ), (∀ t, 0 ≤ η t) → BddAbove (Set.range η) → Measurable η →
    Function.support η ⊆ Set.Icc 0 1 →
    ∀ (q : ℕ), 1 ≤ q → ∀ (x : ℝ), 1 ≤ x →
      (∫ α in (0 : ℝ)..1, ‖S η q x α‖ ^ 2) ≤
        (S (fun t => η t ^ 2) q x 0).re * log x

/-- LEAF. Tao 2012, page 17, proof of Lemma 4.5, first display.
Plancherel identifies the global L2 integral with the sum of squared coefficients. -/
theorem global_plancherel (η : ℝ → ℝ) (q : ℕ) (x : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖S η q x α‖ ^ 2) =
      ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ^ 2 := by
  have hD (α : ℝ) : ‖D 1 α‖ ^ 2 = 1 := by
    simp [D, ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hm : meso η q x 1 = ∫ α in (0 : ℝ)..1, ‖S η q x α‖ ^ 2 := by
    unfold meso
    simp_rw [hD, mul_one]
  have hc : corr η q x 1 1 = ∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ^ 2 := by
    unfold corr
    have hnm (n m : ℕ) : n + 1 = m + 1 ↔ m = n := by omega
    simp_rw [hnm]
    apply sum_congr rfl
    intro n hn
    rw [sum_ite_eq']
    simp [hn, sq]
  have h := plancherel_corr η q x 1
  rw [hm] at h
  simpa only [Finset.Icc_self, sum_singleton, hc] using h

/-- LEAF. Tao 2012, page 17, final sentence of the proof of Lemma 4.5.
The inequality Lambda squared at most Lambda log x bounds the diagonal sum. -/
theorem diagonal_log_bound (η : ℝ → ℝ) (q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ range (⌊x⌋₊ + 1), coef η q x n ^ 2) ≤
      (S (fun t => η t ^ 2) q x 0).re * log x := by
  have hs0 : (S (fun t => η t ^ 2) q x 0).re =
      ∑ n ∈ range (⌊x⌋₊ + 1), coef (fun t => η t ^ 2) q x n := by
    simp [S, ee]
  rw [hs0, sum_mul]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [coef]
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff (by linarith : 0 ≤ x)).mp (by simpa [Nat.lt_succ_iff] using hn)
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ log x := ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) hnx)
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  unfold coef
  split_ifs
  · simp only [mul_one]
    calc (ArithmeticFunction.vonMangoldt n * η (n / x)) ^ 2 =
        ArithmeticFunction.vonMangoldt n * (ArithmeticFunction.vonMangoldt n * η (n / x)^2) := by ring
      _ ≤ log x * (ArithmeticFunction.vonMangoldt n * η (n / x)^2) :=
        mul_le_mul_of_nonneg_right hΛ (mul_nonneg hΛ0 (sq_nonneg _))
      _ = _ := by ring
  · simp

/-- Lemma 4.5 assembled from the two leaves with no sorry in the assembly. -/
theorem lemma4_5 : Lemma4_5 := by
  intro η _ _ _ _ q _ x hx
  rw [global_plancherel]
  exact diagonal_log_bound η q hx

/-- A nonzero concrete cutoff satisfying the Section 4 context on Tao 2012 page 15.
It takes the value one half at one half. -/
theorem triangular_cutoff_admissible : (∀ t : ℝ, 0 ≤ max 0 (min t (1 - t))) ∧
    BddAbove (Set.range (fun t : ℝ => max 0 (min t (1 - t)))) ∧
    Measurable (fun t : ℝ => max 0 (min t (1 - t))) ∧
    Function.support (fun t : ℝ => max 0 (min t (1 - t))) ⊆ Set.Icc 0 1 ∧
    max (0 : ℝ) (min (1 / 2) (1 - 1 / 2)) = 1 / 2 := by
  refine ⟨fun t => le_max_left _ _, ?_, ?_, ?_, by norm_num⟩
  · refine ⟨1, ?_⟩
    rintro y ⟨t, rfl⟩
    apply max_le (by norm_num)
    have h1 := min_le_left t (1 - t)
    have h2 := min_le_right t (1 - t)
    linarith
  · fun_prop
  · intro t ht
    have ht' : max 0 (min t (1 - t)) ≠ 0 := ht
    constructor
    · by_contra ht0
      apply ht'
      apply max_eq_left
      exact (min_le_left _ _).trans (by linarith)
    · by_contra ht1
      apply ht'
      apply max_eq_left
      exact (min_le_right _ _).trans (by linarith)

end LeanLab.Tao2012.Decomp137b
