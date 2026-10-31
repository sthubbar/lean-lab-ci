/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Explicit ordered simplex interfaces for the remaining change of variables.
The general identities are cited propositions, not proved results.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.RecursionFacts
import LeanLab.Akeno2026.Thm12Numerics
import LeanLab.Akeno2026.SieveCTables
import LeanLab.Akeno2026.T6Certified
import LeanLab.Akeno2026.FIntegral

namespace LeanLab.Akeno2026.Appendix
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026.SieveFns
open LeanLab.Akeno2026.Thm12Numerics

/-- Use the first n coordinates and set the last coordinate to one minus their sum. -/
noncomputable def simplexCoords {n : ℕ} (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 - ∑ i, v i) v

/-- The ordered simplex with all coordinates in the paper's closed interval. -/
def orderedSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {v | (∀ i, simplexCoords v i ∈ Icc (1 / s) 1) ∧ Monotone (simplexCoords v)}

/-- Lebesgue integration in the first n coordinates, as the du convention on page 36. -/
noncomputable def simplexIntegral (n : ℕ) (s : ℝ) (W : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  ∫ v in orderedSimplex n s, W (simplexCoords v) / ∏ i, simplexCoords v i

/-- Cited page 36 identity for c_r. This general dimensional identity is unproved. -/
def CRecursionSimplex : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s : ℝ, 0 < s →
    cR (n + 1) s = simplexIntegral n s (fun _ => 1)

/-- Cited page 36 Kuhn reduction. This general dimensional identity is unproved. -/
def KuhnSimplexReduction : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s t : ℝ, 1 < t → t < s →
    simplexIntegral n s (kuhnG t) =
      cR (n + 1) t + t / 2 * ∫ u in (t - 1)..(t * (1 - 1 / s)), cR n u / (u * (t - u))

theorem simplexCoords_sum {n : ℕ} (v : Fin n → ℝ) : ∑ i, simplexCoords v i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [simplexCoords]

theorem orderedSimplex_nonempty : (orderedSimplex 1 4).Nonempty := by
  let v : Fin 1 → ℝ := fun _ => 1 / 4
  have h0 : simplexCoords v (0 : Fin 2) = 1 / 4 := by
    change (Fin.lastCases (1 - ∑ i, v i) v (Fin.castSucc (0 : Fin 1)) : ℝ) = 1 / 4
    rw [Fin.lastCases_castSucc]
  have h1 : simplexCoords v (1 : Fin 2) = 3 / 4 := by
    change (Fin.lastCases (1 - ∑ i, v i) v (Fin.last 1) : ℝ) = 3 / 4
    rw [Fin.lastCases_last]
    norm_num [v]
  refine ⟨v, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [h0, h1]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [h0, h1] at *

/-- The r = 2 simplex integral in the coordinate convention of page 36. -/
theorem cR_two_simplex {s : ℝ} (hs : 2 ≤ s) :
    cR 2 s = ∫ u in (1 / s : ℝ)..(1 / 2 : ℝ), 1 / (u * (1 - u)) := by
  have hs0 : 0 < s := by linarith
  have ha : 0 < 1 / s := by positivity
  have hab : (1 / s : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hs
  have h := (LeanLab.Akeno2026.FIntegral.weight_both ha hab (by norm_num : (1 / 2 : ℝ) < 1)).1
  have heq : (∫ u in (1 / s : ℝ)..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
      ∫ u in (1 / s : ℝ)..(1 / 2 : ℝ), u⁻¹ + (1 - u)⁻¹ := by
    apply integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hu1 : 1 - u ≠ 0 := by linarith [hu.2]
    field_simp [hu0, hu1]
    ring
  rw [cR_two_eq_log hs, heq, h]
  have hp : 0 < (1 / 2 : ℝ) / (1 / s) := by positivity
  have hq : 0 < ((1 : ℝ) - 1 / s) / (1 - 1 / 2) := by
    apply div_pos
    · linarith [hab]
    · norm_num
  rw [← log_mul (ne_of_gt hp) (ne_of_gt hq)]
  congr 1
  field_simp [ne_of_gt hs0]
  ring

/-- The cited Kuhn reduction gives the T5 formula used in the numeric certification. -/
theorem T5_formula_of_reduction (h : KuhnSimplexReduction) :
    simplexIntegral 4 33.5 (kuhnG 9.5) = T5kuhn 33.5 9.5 := by
  simpa only [T5kuhn] using h 4 (by norm_num) 33.5 9.5 (by norm_num) (by norm_num)

/-- The cited Kuhn reduction gives the T6 formula used in the numeric certification. -/
theorem T6_formula_of_reduction (h : KuhnSimplexReduction) :
    simplexIntegral 5 33.5 (kuhnG 9.5) = T6Certified.T6kuhn 33.5 9.5 := by
  simpa only [T6Certified.T6kuhn] using h 5 (by norm_num) 33.5 9.5 (by norm_num) (by norm_num)

end LeanLab.Akeno2026.Appendix
