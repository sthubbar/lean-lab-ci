/-
P0068 Zhan 1991, page 267 read for (3.12) by page 269: the statement of the LEAF
`holder_312_leaf_S9` of SPLIT_prop2_312_S9.lean, branch claude/Zhan1991-S9-07-prop2-312-split,
PROVED. Burst 20261124, session S9, unit C-extra-2. Hölder with exponents `4, 4, 2` in `t`
for each character, done as two Cauchy steps, then the same over the characters. This file
imports only Cauchy312Proof_S9 so that it does not need the S9-07 branch; the statement is
copied word for word. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.Cauchy312Proof_S9

namespace LeanLab.Zhan1991
open Finset Real MeasureTheory

noncomputable section

/-- `x^{1/4} = √√x` for `x ≥ 0`. -/
theorem rpow_quarter_312_S9 {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]; norm_num

/-- Hölder with exponents `4, 4, 2` for finite sums of nonnegative reals, as two Cauchy steps. -/
theorem sum_holder442_312_S9 {ι : Type*} (s : Finset ι) (a b c : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) :
    ∑ i ∈ s, Real.sqrt (Real.sqrt (a i) * Real.sqrt (b i)) * Real.sqrt (c i)
      ≤ Real.sqrt (Real.sqrt (∑ i ∈ s, a i)) * Real.sqrt (Real.sqrt (∑ i ∈ s, b i)) *
        Real.sqrt (∑ i ∈ s, c i) := by
  calc _ ≤ Real.sqrt (∑ i ∈ s, Real.sqrt (a i) * Real.sqrt (b i)) *
        Real.sqrt (∑ i ∈ s, c i) :=
        Real.sum_sqrt_mul_sqrt_le s (fun i => by positivity) hc
    _ ≤ Real.sqrt (Real.sqrt (∑ i ∈ s, a i) * Real.sqrt (∑ i ∈ s, b i)) *
        Real.sqrt (∑ i ∈ s, c i) := by
        gcongr
        exact Real.sum_sqrt_mul_sqrt_le s ha hb
    _ = _ := by rw [Real.sqrt_mul (Real.sqrt_nonneg _)]

/-- PROVED: the statement of the LEAF `holder_312_leaf_S9`, page 267, the two applications of
Hölder's inequality in the proof of Proposition 2, over `[T₂, 2T₂]`. Same statement. -/
theorem holder_312_proof_S9 (Nv : Fin 20 → ℝ) (q : ℕ) [NeZero q] (i j : Fin 20) (hij : i ≠ j)
    (T2 : ℝ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖fj (i.val + 1) (Nv i) χ (1 / 2 + t * Complex.I)‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 4) ^ (1 / 4 : ℝ) *
        Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, fj (k.val + 1) (Nv k) χ
              (1 / 2 + t * Complex.I)‖ ^ 2) := by
  -- continuity of the single factors
  have hcont : ∀ (k : Fin 20) (χ : DirichletCharacter ℂ q),
      Continuous (fun t : ℝ => ‖fj (k.val + 1) (Nv k) χ (1 / 2 + t * Complex.I)‖) := by
    intro k χ
    have h := prodFJ_continuous_312_S9 Nv {k} χ
    simp only [Finset.prod_singleton] at h
    exact h.norm
  have hG : ∀ χ : DirichletCharacter ℂ q,
      Continuous (fun t : ℝ => ‖∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, fj (k.val + 1) (Nv k) χ
        (1 / 2 + t * Complex.I)‖) := fun χ => (prodFJ_continuous_312_S9 Nv _ χ).norm
  set fi := fun (χ : DirichletCharacter ℂ q) (t : ℝ) =>
    ‖fj (i.val + 1) (Nv i) χ (1 / 2 + t * Complex.I)‖ with hfi
  set fjj := fun (χ : DirichletCharacter ℂ q) (t : ℝ) =>
    ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ with hfjj
  set g := fun (χ : DirichletCharacter ℂ q) (t : ℝ) =>
    ‖∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, fj (k.val + 1) (Nv k) χ (1 / 2 + t * Complex.I)‖
    with hg
  have hsplit : ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ = fi χ t * fjj χ t * g χ t := by
    intro χ t
    simp only [hfi, hfjj, hg]
    rw [← norm_mul, ← norm_mul]
    unfold Fprod
    rw [← Finset.prod_mul_prod_compl ({i, j} : Finset (Fin 20)), Finset.prod_pair hij]
  -- the pointwise step for each character
  have hpt : ∀ χ : DirichletCharacter ℂ q,
      ∫ t in Set.uIoc T2 (2 * T2), fi χ t * fjj χ t * g χ t ≤
        Real.sqrt (Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), fi χ t ^ 4) *
          Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), fjj χ t ^ 4)) *
        Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), g χ t ^ 2) := by
    intro χ
    have c1 : ∫ t in Set.uIoc T2 (2 * T2), fi χ t * fjj χ t * g χ t ≤
        Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), (fi χ t * fjj χ t) ^ 2) *
          Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), g χ t ^ 2) :=
      integral_cauchy_Ioc_312_S9 (fun t => fi χ t * fjj χ t) (g χ)
        ((hcont i χ).mul (hcont j χ)) (hG χ) (fun t => by positivity) (fun t => by positivity)
        _ _
    have c2 : ∫ t in Set.uIoc T2 (2 * T2), fi χ t ^ 2 * fjj χ t ^ 2 ≤
        Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), (fi χ t ^ 2) ^ 2) *
          Real.sqrt (∫ t in Set.uIoc T2 (2 * T2), (fjj χ t ^ 2) ^ 2) :=
      integral_cauchy_Ioc_312_S9 (fun t => fi χ t ^ 2) (fun t => fjj χ t ^ 2)
        ((hcont i χ).pow 2) ((hcont j χ).pow 2) (fun t => by positivity)
        (fun t => by positivity) _ _
    have e1 : ∀ t, (fi χ t * fjj χ t) ^ 2 = fi χ t ^ 2 * fjj χ t ^ 2 := fun t => by ring
    have e2 : ∀ t, (fi χ t ^ 2) ^ 2 = fi χ t ^ 4 := fun t => by ring
    have e3 : ∀ t, (fjj χ t ^ 2) ^ 2 = fjj χ t ^ 4 := fun t => by ring
    simp only [e1] at c1
    simp only [e2, e3] at c2
    calc ∫ t in Set.uIoc T2 (2 * T2), fi χ t * fjj χ t * g χ t ≤ _ := c1
      _ ≤ _ := by gcongr
  have hnn2 : ∀ (h : DirichletCharacter ℂ q → ℝ → ℝ) (n : ℕ) (χ : DirichletCharacter ℂ q),
      (∀ t, 0 ≤ h χ t) → 0 ≤ ∫ t in Set.uIoc T2 (2 * T2), h χ t ^ n :=
    fun h n χ hh => integral_nonneg (fun t => pow_nonneg (hh t) n)
  rw [rpow_quarter_312_S9 (Finset.sum_nonneg (fun χ _ => hnn2 fi 4 χ (fun t => by positivity))),
    rpow_quarter_312_S9 (Finset.sum_nonneg (fun χ _ => hnn2 fjj 4 χ (fun t => by positivity)))]
  calc _ = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2), fi χ t * fjj χ t * g χ t := by
        simp only [hsplit]
    _ ≤ _ := Finset.sum_le_sum (fun χ _ => hpt χ)
    _ ≤ _ := sum_holder442_312_S9 _ _ _ _
          (fun χ => hnn2 fi 4 χ (fun t => by positivity))
          (fun χ => hnn2 fjj 4 χ (fun t => by positivity))
          (fun χ => hnn2 g 2 χ (fun t => by positivity))

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.rpow_quarter_312_S9
#print axioms LeanLab.Zhan1991.sum_holder442_312_S9
#print axioms LeanLab.Zhan1991.holder_312_proof_S9
