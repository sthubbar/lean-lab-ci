import LeanLab.Ternary78.GammaWeights

/-
AI wrote this Lean code. Binary Goldbach is open.
These are consequences for the existing threshold MODEL, not a circle method proof.
The numerical certificate is an explicit premise. No such 0.985 certificate is claimed.
-/

namespace LeanLab.Ternary78.Bennett
open Real
open LeanLab.Ternary78.Threshold

/-- CONDITIONAL ON BennettThm1_1. A certified sufficiently large finite lower sum
propagates to the next model barrier. -/
theorem model_gap_of_bennett_certificate
    {Ncount : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 Ncount Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ w : ι → ℝ)
    (t f : ℕ → ℝ) (ht : Monotone t)
    (hf : ∀ i, f (i + 1) ≤ f i) (hf0 : ∀ i, 0 ≤ f i) (k : ℕ)
    (hcount : ∀ i, 0 < i → i ≤ k →
      Ncount q χ (t i) = (heightSet z γ t i).card)
    (hw : ∀ i a, 0 < i → a ∈ z → |γ a| ≤ t i → f i ≤ w a)
    {S c N : ℝ} (hS : (∑ a ∈ heightSet z γ t k, w a) ≤ S)
    (hcert : 0.985 ≤ weightedCount (gridLower χ t) f k)
    (hc : 0 < c) (hc2 : c ≤ 0.495462) (hN0 : 0 < N) (hN : N ≤ 8.875e30) :
    m78 * (c * N) ^ (1 / 8 : ℝ) < S * sqrt 300000 := by
  have hlow := finite_weighted_lower_of_bennett hB hq hq1 χ hχ z γ w t f ht hf hf0 k hcount hw
  exact gap_open (hcert.trans (hlow.trans hS)) hc hc2 hN0 hN

#print axioms model_gap_of_bennett_certificate

/-- CONDITIONAL ON BennettThm1_1. This connects the actual 7/8 Gamma zero sum
to the model barrier. A numerical certificate is still an explicit premise. -/
theorem model_gap_of_gamma_bennett
    {Ncount : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {q : ℕ} [NeZero q]
    (hB : BennettThm1_1 Ncount 300000) (hq : q ≤ 300000) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ : ι → ℝ)
    (t : ℕ → ℝ) (ht : Monotone t) (ht0 : ∀ i, 0 ≤ t i) (k : ℕ)
    (hcount : ∀ i, 0 < i → i ≤ k →
      Ncount q χ (t i) = (heightSet z γ t i).card)
    {S c N : ℝ} (hS0 : 0 ≤ S)
    (hS : (∑' a, ENNReal.ofReal ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) +
      (γ a : ℂ) * Complex.I)‖) ≤ ENNReal.ofReal S)
    (hcert : 0.985 ≤ weightedCount (gridLower χ t)
      (fun i => ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (t i : ℂ) * Complex.I)‖) k)
    (hc : 0 < c) (hc2 : c ≤ 0.495462) (hN0 : 0 < N) (hN : N ≤ 8.875e30) :
    m78 * (c * N) ^ (1 / 8 : ℝ) < S * sqrt 300000 := by
  have hlow := gamma_tsum_lower_of_bennett hB hq hq1 χ hχ z γ
    (by norm_num : (0 : ℝ) < 7 / 8) t ht ht0 k hcount
  have hbound := (ENNReal.ofReal_le_ofReal hcert).trans (hlow.trans hS)
  exact gap_open ((ENNReal.ofReal_le_ofReal_iff hS0).mp hbound) hc hc2 hN0 hN

#print axioms model_gap_of_gamma_bennett

/-- A lower certificate at most 1/2 cannot by itself force the model gap.
The witness S = 1/2 satisfies the closing inequality at the verification endpoint. -/
theorem weak_certificate_has_closing_model {B : ℝ} (hB : B ≤ 1 / 2) :
    ∃ S : ℝ, B ≤ S ∧ S < 0.985 ∧
      S * sqrt 300000 ≤ m78 * (0.495461 * 8.875e30 : ℝ) ^ (1 / 8 : ℝ) := by
  refine ⟨1 / 2, hB, by norm_num, ?_⟩
  apply closes_of_ge (by norm_num) (by norm_num)
    (by unfold m78 LeanLab.Ternary78.Hybrid.margin; norm_num) (by norm_num)
  have hsqrt : sqrt (300000 : ℝ) ≤ 548 := by
    rw [sqrt_le_left (by norm_num)]
    norm_num
  have hm : (0.079684 : ℝ) ≤ m78 := LeanLab.Ternary78.Hybrid.margin_bounds.1.le
  calc
    ((1 / 2 : ℝ) * sqrt 300000 / m78) ^ 8 / 0.495461 ≤
        ((1 / 2 : ℝ) * 548 / 0.079684) ^ 8 / 0.495461 := by
      gcongr
    _ ≤ 8.875e30 := by norm_num

#print axioms weak_certificate_has_closing_model

end LeanLab.Ternary78.Bennett
