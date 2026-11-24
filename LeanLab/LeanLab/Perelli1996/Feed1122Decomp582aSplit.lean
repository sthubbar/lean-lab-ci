/-
Perelli 1996, pages 484, 485 and 487, equations 18 through 25 and 31.
Feed split of Decomp582a.leaf_short_character_mean: the proved Gallagher
reduction characterEnergy_gallagher plus one window variance LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp582a
import LeanLab.Perelli1996.Mean103

namespace LeanLab.Perelli1996.Feed1122Decomp582aSplit
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
open LeanLab.Perelli1996.Decomp582a
open scoped ArithmeticFunction.vonMangoldt
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Pages 484 and 485 equations 18 through 25, applied on page 487 below
equation 31, after the Gallagher reduction through Perelli and Pintz 1993 page 47
equation 21. Class HARD. For every modulus q up to a power of log N and any
windows of length between q Q over four and q Q over two, with Q the mean order,
the normalized short window variances of psi of x and chi, centered by the principal
term, sum over all characters to O of N times log N to the minus D. The proof in the
paper uses the truncated explicit formula, the zero free region and the cited density
estimate hDensity. CONDITIONAL ON the displayed density estimate. -/
theorem leaf_window_variance (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d)
    (hDensity : ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d)
    (c B D ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hD : 0 < D) (hε : 0 < ε) :
    ∃ K N₀ : ℝ, 0 < K ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
      ∀ L : DirichletCharacter ℂ q → ℕ,
        (∀ χ, 0 < L χ ∧ (q : ℝ) * meanOrder F N H B / 4 ≤ L χ ∧
          (L χ : ℝ) ≤ (q : ℝ) * meanOrder F N H B / 2) →
        ((q : ℝ) / q.totient) *
            (4 * Real.pi ^ 2 / ((q : ℝ) * meanOrder F N H B) ^ 2) *
          ∑ χ : DirichletCharacter ℂ q, ∑ m ∈ range (⌊c * N⌋₊ + 1 + L χ),
            ‖LeanLab.PNTPort.Gallagher.win
              (fun n => (Λ n : ℂ) * χ n - if χ = 1 then 1 else 0)
              (⌊c * N⌋₊ + 1) (L χ) m‖ ^ 2 ≤
          K * N * Real.log N ^ (-D) := by
  sorry

/-- Page 487 below equation 31. For large N the mean order is at least two
on the Theorem 2 window, so the Gallagher reduction applies. -/
theorem meanOrder_ge_two (F : ℤ[X]) (hF : Admissible F) (B ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H → 2 ≤ meanOrder F N H B := by
  let δ := 1 / (12 * (F.natDegree : ℝ)) + ε / 2
  have hk : 0 < (F.natDegree : ℝ) := by
    exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NQ, hNQ, hq⟩ := Section3.power_error_log_saving δ B hδ
  refine ⟨max NQ ((2 : ℝ) ^ (1 / δ)), hNQ.trans (le_max_left _ _), ?_⟩
  intro N H hN hH
  have hNQ' : NQ ≤ N := (le_max_left _ _).trans hN
  have hN2 : (2 : ℝ) ^ (1 / δ) ≤ N := (le_max_right _ _).trans hN
  have hN3 : 3 ≤ N := hNQ.trans hNQ'
  have hN1 : 1 ≤ N := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have htwo : 2 ≤ N ^ δ := by
    calc
      (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
        rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ N ^ δ := Real.rpow_le_rpow (by positivity) hN2 hδ.le
  have hh : N ^ (2 * δ) ≤ H := by
    convert hH using 1
    dsimp [δ]
    congr 1
    field_simp
    ring
  calc
    2 ≤ N ^ δ := htwo
    _ ≤ H * Real.log N ^ (-B) := hq N H hNQ' hh
    _ ≤ meanOrder F N H B := by
      unfold meanOrder
      exact mul_le_mul_of_nonneg_right
        (le_self_pow₀ hH1 (by have := hF.1; omega))
        (Real.rpow_nonneg (Real.log_nonneg hN1) _)

/-- Assembly. Pages 484, 485 and 487. The statement of
Decomp582a.leaf_short_character_mean, proved from characterEnergy_gallagher,
meanOrder_ge_two and leaf_window_variance. No sorry in this assembly. -/
theorem leaf_short_character_mean_assembled (F : ℤ[X]) (hF : Admissible F)
    (C d : ℝ) (hC : 0 < C) (hd : 0 < d)
    (hDensity : ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
        (∀ χ ρ, ρ ∈ Z χ → DirichletCharacter.LFunction χ ρ = 0 ∧
          σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        (∑ χ : DirichletCharacter ℂ q,
          ∑ ρ ∈ Z χ, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
          C * ((q : ℝ) * T) ^ (12 * (1 - σ) / 5) *
            Real.log ((q : ℝ) * T) ^ d)
    (c B D ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hD : 0 < D) (hε : 0 < ε) :
    ∃ K N₀ : ℝ, 0 < K ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log N ^ B →
        characterEnergy ⌊c * N⌋₊ q (meanOrder F N H B) ≤
          K * N * Real.log N ^ (-D) := by
  obtain ⟨K, NW, hK, hNW, hw⟩ :=
    leaf_window_variance F hF C d hC hd hDensity c B D ε hc hB hD hε
  obtain ⟨NM, hNM, hm⟩ := meanOrder_ge_two F hF B ε hε
  refine ⟨K, max NW NM, hK, hNW.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu q hq1 hqP
  have hNW' : NW ≤ N := (le_max_left _ _).trans hN
  have hNM' : NM ≤ N := (le_max_right _ _).trans hN
  have hQ2 := hm N H hNM' hH
  have hQ : 0 < meanOrder F N H B := by linarith
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have horder : 2 ≤ (q : ℝ) * meanOrder F N H B := by nlinarith
  obtain ⟨L, hL, hbound⟩ :=
    characterEnergy_gallagher ⌊c * N⌋₊ q hq1 (meanOrder F N H B) hQ horder
  exact hbound.trans (hw N H hNW' hH hHu q hq1 hqP L hL)

end
end LeanLab.Perelli1996.Feed1122Decomp582aSplit
