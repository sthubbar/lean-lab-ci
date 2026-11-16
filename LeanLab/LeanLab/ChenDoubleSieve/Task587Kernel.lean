import LeanLab.ChenDoubleSieve.Task587Tail

/-!
Kernel tools for certified tails in Wu 2004 Lemma 5.2 page 26.
Source: https://arxiv.org/abs/0705.1652.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587
open Wu04Functional

/-- A positive box and arguments above one give an integrable Buchstab kernel.
Wu 2004 pages 9 and 26, derived compact-domain tool. -/
theorem kernel_integrable_above_one {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (lo hi : Fin (n + 2) → ℝ) (φ : ℝ) (hlo : ∀ j, 0 < lo j)
    (harg : ∀ x ∈ domain lo hi, 1 ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    IntegrableOn (fun x => ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩) /
      ((∏ j, x j) * x ⟨n, by omega⟩)) (domain lo hi) volume := by
  have hp (x : Fin (n + 2) → ℝ) (hx : x ∈ domain lo hi) (j : Fin (n + 2)) :
      0 < x j := (hlo j).trans_le (hx.2 j).1
  apply ContinuousOn.integrableOn_compact (Wu04I1.domain_isCompact _ _)
  have ha : ContinuousOn (fun x : Fin (n + 2) → ℝ =>
      (φ - ∑ j, x j) / x ⟨n, by omega⟩) (domain lo hi) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun x hx => (hp x hx _).ne')
  have hw : ContinuousOn (fun x => ω ((φ - ∑ j, x j) / x ⟨n, by omega⟩))
      (domain lo hi) := hω.1.comp ha harg
  apply hw.div (by fun_prop)
  intro x hx
  exact (mul_pos (prod_pos fun j _ => hp x hx j) (hp x hx _)).ne'

/-- A reciprocal polynomial controls every Buchstab tail whose arguments are at least four.
Wu 2004 pages 9 and 26, derived uniform polynomial reduction. -/
theorem integral_le_poly_of_argument_four {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (lo hi : Fin (n + 2) → ℝ) (φ : ℝ) (hlo : ∀ j, 0 < lo j)
    (P : (Fin (n + 2) → ℝ) → ℝ) (hP : IntegrableOn P (domain lo hi) volume)
    (hmajor : ∀ x ∈ domain lo hi, 1 / ((∏ j, x j) * x ⟨n, by omega⟩) ≤ P x)
    (harg : ∀ x ∈ domain lo hi, 4 ≤ (φ - ∑ j, x j) / x ⟨n, by omega⟩) :
    buchstabIntegral ω n lo hi φ ≤ (563 / 1000 : ℝ) * ∫ x in domain lo hi, P x := by
  have hf := kernel_integrable_above_one hω lo hi φ hlo
    (fun x hx => (by norm_num : (1 : ℝ) ≤ 4).trans (harg x hx))
  have hm := setIntegral_mono_on hf (hP.const_mul (563 / 1000 : ℝ))
    (Wu04I1.domain_isCompact _ _).measurableSet (fun x hx => by
      have hp (j : Fin (n + 2)) : 0 < x j := (hlo j).trans_le (hx.2 j).1
      have hd : 0 < (∏ j, x j) * x ⟨n, by omega⟩ :=
        mul_pos (prod_pos fun j _ => hp j) (hp _)
      have hw := div_le_div_of_nonneg_right (buchstab_le_563 hω (harg x hx)) hd.le
      calc
        _ ≤ (563 / 1000 : ℝ) / ((∏ j, x j) * x ⟨n, by omega⟩) := hw
        _ = (563 / 1000 : ℝ) * (1 / ((∏ j, x j) * x ⟨n, by omega⟩)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmajor x hx) (by norm_num))
  simpa only [buchstabIntegral, MeasureTheory.integral_const_mul] using hm

end LeanLab.ChenDoubleSieve.Task587
