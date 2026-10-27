import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.SigmaKernel

/-!
# Elementary sign bounds for Wu 2004 Proposition 3

Source: https://arxiv.org/pdf/0705.1652, page 14, equation 3.21,
page 22, Lemma 5.1, and page 30, Table 1.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set
namespace LeanLab.ChenDoubleSieve.Wu04Functional

/-- The three terms of Xi1 have nonnegative signs throughout the integration interval. -/
theorem Xi1_nonneg {s sp t : ℝ} (hp : Admissible3 s sp) (ht : 1 ≤ t) :
    0 ≤ Xi1 s sp t := by
  obtain ⟨hs2, hs3, hsp3, hsp5, hratio⟩ := hp
  have hs0 : 0 < s := by linarith
  have hP0 : 0 < (s - 1) * (sp - 1) := mul_pos (by linarith) (by linarith)
  have hP8 : (s - 1) * (sp - 1) ≤ 8 := by
    calc (s - 1) * (sp - 1) ≤ 2 * 4 :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      _ = 8 := by norm_num
  have hlog0 : 0 ≤ log (16 / ((s - 1) * (sp - 1))) := by
    apply log_nonneg
    rw [le_div_iff₀ hP0]
    linarith
  have hterm0 : 0 ≤ Wu04Integral.sigma0 t / (2 * t) * log (16 / ((s - 1) * (sp - 1))) :=
    mul_nonneg (div_nonneg (Wu04Integral.sigma0_nonneg ht) (by linarith)) hlog0
  have hterm1 : 0 ≤ ind (sp - 2) 3 t / (2 * t) * log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) := by
    by_cases hI : sp - 2 ≤ t ∧ t ≤ 3
    · have hlog : 0 ≤ log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) := by
        apply log_nonneg
        rw [le_div_iff₀ hP0]
        have hb : (s - 1) * (sp - 1) ≤ (t + 1) * (t + 1) :=
          mul_le_mul (by linarith [hI.1]) (by linarith [hI.1]) (by linarith) (by linarith)
        nlinarith
      simp only [ind, if_pos hI]
      exact mul_nonneg (by positivity) hlog
    · simp only [ind, if_neg hI, zero_div, zero_mul, le_refl]
  have hterm2 : 0 ≤ ind (sp - sp / s - 1) (sp - 2) t / (2 * t) *
      log ((t + 1) / ((s - 1) * (sp - 1 - t))) := by
    by_cases hI : sp - sp / s - 1 ≤ t ∧ t ≤ sp - 2
    · have hden : 0 < (s - 1) * (sp - 1 - t) := mul_pos (by linarith) (by linarith [hI.2])
      have hlog : 0 ≤ log ((t + 1) / ((s - 1) * (sp - 1 - t))) := by
        apply log_nonneg
        rw [le_div_iff₀ hden]
        have hd : sp - 1 - t ≤ sp / s := by linarith [hI.1]
        have hm := (le_div_iff₀ hs0).mp hd
        nlinarith
      simp only [ind, if_pos hI]
      exact mul_nonneg (by positivity) hlog
    · simp only [ind, if_neg hI, zero_div, zero_mul, le_refl]
  unfold Xi1
  linarith

/-- All five Proposition 3 rows satisfy every printed hypothesis. -/
theorem tableSp_admissible : ∀ i : Fin 5,
    Admissible3 (grid ⟨i.val + 5, by omega⟩) (tableSp i) := by
  intro i
  fin_cases i <;> norm_num [Admissible3, grid, tableSp]

/-- In the Proposition 3 Table 1 rows the Buchstab argument is always at least two. -/
theorem I1_argument_ge_two {s sp φ : ℝ} (hs : (5 / 2 : ℝ) ≤ s) (hsp : 0 < sp)
    (hφ : 2 ≤ φ) {x : Fin 3 → ℝ} (hx : x ∈ domain (fun _ => 1 / sp) (fun _ => 1 / s)) :
    2 ≤ (φ - ∑ j, x j) / x 1 := by
  have hs0 : 0 < s := by linarith
  have hxpos : 0 < x 1 := (one_div_pos.mpr hsp).trans_le (hx.2 1).1
  rw [le_div_iff₀ hxpos]
  have hx0 := (hx.2 0).2
  have hx1 := (hx.2 1).2
  have hx2 := (hx.2 2).2
  have hrec : (5 : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hs0]; linarith
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at *
  norm_num at hx0 hx1 hx2 ⊢
  rw [div_eq_mul_inv] at hrec
  linarith

end LeanLab.ChenDoubleSieve.Wu04Functional

#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.Xi1_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.tableSp_admissible
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.I1_argument_ge_two
