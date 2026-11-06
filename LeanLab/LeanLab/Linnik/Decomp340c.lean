/-
Finite zero families for the integrated detector interface.
The intended application is Gallagher 1970 pp.333 and 336 before display 25.
The written argument was read from rendered source pages 333, 335 and 336.
Source https://doi.org/10.1007/BF01403187
AI wrote the Lean code. Codex task340. Goldbach is open.
-/
import LeanLab.Linnik.Decomp1532b

open Finset MeasureTheory Complex
open scoped Classical
open LeanLab.Linnik.Decomp1532b

namespace LeanLab.Linnik.Decomp340c

/-- Primitive zero counts in the right half strip are the cardinalities
of finite families with exactly the zero and height predicates in zeroCount. -/
theorem exists_zeroCount_finset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) :
    ∃ S : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ S ↔ χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      S.card = zeroCount χ σ T := by
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq : q = 1
    · exact Or.inl hq
    · right
      intro hχ
      apply hq
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have hnt {ρ : ℂ} (hz : χ.LFunction ρ = 0) (hβ : σ ≤ ρ.re) :
      LeanLab.HardyLittlewood1923.U1479.IsNTZero χ ρ := by
    refine ⟨hz, by linarith, ?_⟩
    by_contra h
    have hre : 1 ≤ ρ.re := le_of_not_gt h
    rcases hψ with rfl | hχ
    · rw [DirichletCharacter.LFunction_modOne_eq] at hz
      exact riemannZeta_ne_zero_of_one_le_re hre hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre hz
  obtain ⟨S₀, hS₀⟩ := LeanLab.HardyLittlewood1923.U1479.exists_zero_finset
    LeanLab.HardyLittlewood1923.U1482.zeroCountUnit hp hT
  let S := S₀.filter (fun ρ => σ ≤ ρ.re)
  have hS (ρ : ℂ) : ρ ∈ S ↔ χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    simp only [S, mem_filter, hS₀]
    constructor
    · rintro ⟨⟨hρ, hγ⟩, hβ⟩
      exact ⟨hρ.1, hβ, hγ⟩
    · rintro ⟨hz, hβ, hγ⟩
      exact ⟨⟨hnt hz hβ, hγ⟩, hβ⟩
  refine ⟨S, hS, ?_⟩
  have heq : {ρ : ℂ | χ.LFunction ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T} = (S : Set ℂ) := by
    ext ρ
    exact (hS ρ).symm
  rw [zeroCount, heq, Set.ncard_coe_finset]

/-- The proved local multiplicity bound also bounds the number of distinct
primitive zeros in the same disc. No zero existence assumption is introduced. -/
theorem primitive_local_zero_card : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ t r : ℝ,
      |t| ≤ T → (χ = 1 → 2 ≤ |t|) → 1 / Real.log T ≤ r → r ≤ 1 / 8 →
      ∀ S : Finset ℂ, (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * t)‖ ≤ r) →
      (S.card : ℝ) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := primitive_local_zero_order_sum
  refine ⟨C, hC, ?_⟩
  intro T hT q hq hqT χ hp t r ht hχ hrlo hrhi S hS
  have hψ : q = 1 ∨ χ ≠ 1 := by
    by_cases hq1 : q = 1
    · exact Or.inl hq1
    · right
      intro he
      apply hq1
      have hh := hp
      rw [DirichletCharacter.isPrimitive_def, he, DirichletCharacter.conductor_one] at hh
      exact hh.symm
  have horder (ρ : ℂ) (hρ : ρ ∈ S) :
      (1 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
    have hw : ρ ≠ 1 := by
      intro he
      have hz := (hS ρ hρ).1
      rw [he] at hz
      rcases hψ with rfl | hχ1
      · rw [DirichletCharacter.LFunction_modOne_eq] at hz
        exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
      · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp) hz
    have hz : analyticOrderNatAt χ.LFunction ρ ≠ 0 := by
      simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨(LeanLab.HardyLittlewood1923.U1482.L_analyticAt χ hw).analyticOrderAt_ne_zero.mpr
          (hS ρ hρ).1,
        LeanLab.HardyLittlewood1923.U1482.L_ord_ne_top χ hψ hw⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  calc
    _ = ∑ _ρ ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) := sum_le_sum horder
    _ ≤ _ := hbound T hT q hqT χ hp t r ht hχ hrlo hrhi S hS

/-- Distinct zeros in a narrow right strip have bounded occupancy in each
vertical height window. The principal character height exclusion remains explicit. -/
theorem primitive_height_window_occupancy : ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → ∀ v r : ℝ,
      |v| ≤ T → (χ = 1 → 2 ≤ |v|) →
      1 / Real.log T ≤ 2 * r → 2 * r ≤ 1 / 8 →
      ∀ S : Finset ℂ,
      (∀ ρ ∈ S, χ.LFunction ρ = 0 ∧ 1 - r ≤ ρ.re ∧ ρ.re ≤ 1) →
      (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
        (fun _ => (1 : ℝ)) v) ≤ C * r * Real.log T := by
  obtain ⟨C, hC, hcard⟩ := primitive_local_zero_card
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT q hq hqT χ hp v r hv hχ hrlo hrhi S hS
  let Z := S.filter (fun ρ => v ∈ Set.Icc (ρ.im - r) (ρ.im + r))
  have hZ (ρ : ℂ) (hρ : ρ ∈ Z) : χ.LFunction ρ = 0 ∧ ‖ρ - (1 + I * v)‖ ≤ 2 * r := by
    obtain ⟨hρS, hρv⟩ := mem_filter.mp hρ
    obtain ⟨hz, hβlo, hβhi⟩ := hS ρ hρS
    have hre : |ρ.re - 1| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have him : |ρ.im - v| ≤ r := abs_le.mpr ⟨by linarith [hρv.2], by linarith [hρv.1]⟩
    refine ⟨hz, ?_⟩
    calc
      _ ≤ |(ρ - (1 + I * v)).re| + |(ρ - (1 + I * v)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |ρ.re - 1| + |ρ.im - v| := by simp
      _ ≤ _ := by linarith
  have heq : (∑ ρ ∈ S, (Set.Icc (ρ.im - r) (ρ.im + r)).indicator
      (fun _ => (1 : ℝ)) v) = (Z.card : ℝ) := by
    simp only [Z, Set.indicator, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [heq]
  have hh := hcard T hT q hqT χ hp v (2 * r) hv hχ hrlo hrhi Z hZ
  convert hh using 1; ring

end LeanLab.Linnik.Decomp340c
