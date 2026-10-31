import LeanLab.BakerHarmanPintz1997.Statements
open scoped Real

namespace LeanLab.BakerHarmanPintz1997
open Finset

/-- LEAF. p. 23, Case L > qT. -/
theorem lemma10_large_L :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

/-- LEAF. p. 24, Case L ≤ qT and (3.38). -/
theorem lemma10_small_L_338 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

/-- LEAF. p. 24, Case L ≤ qT and (3.39). -/
theorem lemma10_small_L_339 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

theorem lemma10_decomposed : Lemma10 := by
  rcases lemma10_large_L with ⟨ε0_1, h_ε0_1, h_large⟩
  rcases lemma10_small_L_338 with ⟨ε0_2, h_ε0_2, h_small_338⟩
  rcases lemma10_small_L_339 with ⟨ε0_3, h_ε0_3, h_small_339⟩
  use min ε0_1 (min ε0_2 ε0_3)
  refine ⟨by positivity, fun ε hε1 hε2 => ?_⟩
  intro A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 h_fam_ok h_prod h_c h_or A hA

  have h_large_spec := h_large ε hε1 (lt_of_lt_of_le hε2 (min_le_left _ _)) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | (c.q : ℝ) * c.T < Ll x}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2) A hA
  have h_small_338_spec := h_small_338 ε hε1 (lt_of_lt_of_le hε2 (le_trans (min_le_right _ _) (min_le_left _ _))) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2.2) (fun x c hc => hc.2.1) A hA
  have h_small_339_spec := h_small_339 ε hε1 (lt_of_lt_of_le hε2 (le_trans (min_le_right _ _) (min_le_right _ _))) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2.2) (fun x c hc => hc.2.1) A hA

  rcases h_large_spec with ⟨C1, X01, h1⟩
  rcases h_small_338_spec with ⟨C2, X02, h2⟩
  rcases h_small_339_spec with ⟨C3, X03, h3⟩

  use max C1 (max C2 C3), max 1 (max X01 (max X02 X03))
  intro x hx c hc
  have hx_ge_1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx_ge_0 : 0 ≤ x := le_trans (by norm_num) hx_ge_1

  have hx1 : X01 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx2 : X02 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
  have hx3 : X03 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))

  have hL_ge_0 : 0 ≤ L x := Real.log_nonneg hx_ge_1
  have H_pos : 0 ≤ x ^ (1 / 2 : ℝ) / L x ^ A := by positivity

  have h_eq_C1 : C1 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C1 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C2 : C2 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C2 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C3 : C3 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C3 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C_max : max C1 (max C2 C3) * (x ^ (1 / 2 : ℝ) / L x ^ A) = max C1 (max C2 C3) * x ^ (1 / 2 : ℝ) / L x ^ A := by ring

  by_cases hL : (c.q : ℝ) * c.T < Ll x
  · have hc_large : c ∈ {c ∈ 𝒮 x | (c.q : ℝ) * c.T < Ll x} := ⟨hc, hL⟩
    have h_ineq := h1 x hx1 c hc_large
    have h_max : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
    have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
    rw [h_eq_C1, h_eq_C_max] at h_mul
    exact le_trans h_ineq h_mul
  · have hL_le : Ll x ≤ (c.q : ℝ) * c.T := not_lt.mp hL
    cases h_or x with
    | inl h_338 =>
      have hc_small : c ∈ {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)} := ⟨hc, hL_le, h_338⟩
      have h_ineq := h2 x hx2 c hc_small
      have h_max : C2 ≤ max C1 (max C2 C3) := le_trans (le_max_left _ _) (le_max_right _ _)
      have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
      rw [h_eq_C2, h_eq_C_max] at h_mul
      exact le_trans h_ineq h_mul
    | inr h_339 =>
      have hc_small : c ∈ {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)} := ⟨hc, hL_le, h_339⟩
      have h_ineq := h3 x hx3 c hc_small
      have h_max : C3 ≤ max C1 (max C2 C3) := le_trans (le_max_right _ _) (le_max_right _ _)
      have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
      rw [h_eq_C3, h_eq_C_max] at h_mul
      exact le_trans h_ineq h_mul

end LeanLab.BakerHarmanPintz1997
