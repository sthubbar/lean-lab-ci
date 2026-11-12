import LeanLab.MissingDigit.Burst8P23

/-!
# Burst 8, Kim's Theorem 1.1 in the range `H ≥ X^{5/8+ε}`, from MSTT as printed

Paper: P0057, J. Kim, arXiv 2412.19975v1. Kim's Proposition 2.1, page 7, quotes
Matomäki, Shao, Tao and Teräväinen, Higher uniformity of arithmetic functions in short
intervals I, arXiv 2204.03754, Theorem 1.1 (iii), for `X^{3/5+ε} ≤ H`. In that theorem, as
checked in versions 1 and 4 of the arXiv text, part (iii) for `d_k` with `k ≥ 4` has
`θ = 5/8`, with the saving `H X^{-cε}`, while part (v), the `θ = 3/5` case for `k ≥ 4`, only
gives `H (log X)^{3k/4 - 1}`. So the cited input supports Proposition 2.1 only for
`X^{5/8+ε} ≤ H`. This file states Proposition 2.1 in that range, `prop_2_1_58`, and assembles
`D4Bound (5 / 8) 7`, Theorem 1.1 with `5/8` in place of `3/5`, from it and the other leaves.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.MissingDigit.Burst8Range58

open Finset Real MeasureTheory Filter
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split LeanLab.MissingDigit.Burst8P2
  LeanLab.MissingDigit.Burst8L17 LeanLab.MissingDigit.Burst8Major
  LeanLab.MissingDigit.Burst8P23

attribute [local instance] Classical.propDecidable

/-- Cited, sorry. MSTT, Forum Math. Pi 11 (2023) e29, arXiv 2204.03754, Theorem 1.1 (iii) with
`k = 4`, `θ = 5/8`, and the phase `e(nα)`, a nilsequence of degree `1` on `ℝ/ℤ`: for
`X^{5/8+ε} ≤ H ≤ X^{1-ε}`, `sup_α |∑ (d₄(n) - d♯₄(n)) e(nα)| ≪_ε H X^{-cε}`. MSTT allow any
fixed `η ≤ 1/40` in `R₄ = X^η`, with constants depending on `η`; Kim takes `η = ε/40`. Here the
sum also contains the single term `n = X`, which is far below `H X^{-cε}`. Encoded with `ε`
small, `c` allowed to depend on `ε`, and explicit `C` and `X₀`. -/
theorem prop_2_1_58 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) → ∀ α : ℝ,
        ‖S4 X H α - S4sharp ε X H α‖ ≤ C * H * (X : ℝ) ^ (-(c * ε)) := by
  sorry

theorem lo_mono {g k : ℕ} (hg : 1 ≤ g) {ε H : ℝ}
    (h : ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H) :
    ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H :=
  le_trans (Real.rpow_le_rpow_of_exponent_le (pow_ge_one_real hg) (by linarith)) h

/-- The major arc leaf in the range `X^{5/8+ε} ≤ H`, from `major_arcs_bound_p4`. -/
theorem major_arcs_bound_58 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ,
    ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  obtain ⟨e, he, h⟩ := major_arcs_bound_p4
  refine ⟨e, he, fun ε hε hεe => ?_⟩
  obtain ⟨g₀, hg₀⟩ := h ε hε hεe
  refine ⟨g₀, fun g b hg hb hbg => ?_⟩
  obtain ⟨C, K, hK⟩ := hg₀ g b hg hb hbg
  exact ⟨C, K, fun k H hk hlo hhi => hK k H hk (lo_mono (by omega) hlo) hhi⟩

/-- The minor arc leaf in the range `X^{5/8+ε} ≤ H`, from `prop_2_5_p3`. -/
theorem prop_2_5_58 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨e, he, h⟩ := prop_2_5_p3
  refine ⟨e, he, fun ε hε hεe => ?_⟩
  obtain ⟨g₀, hg₀⟩ := h ε hε hεe
  refine ⟨g₀, fun g b hg hb hbg η hη => ?_⟩
  obtain ⟨K, hK⟩ := hg₀ g b hg hb hbg η hη
  exact ⟨K, fun k H hk hlo hhi => hK k H hk (lo_mono (by omega) hlo) hhi⟩

/-- Kim, Proposition 2.2 in the range `X^{5/8+ε} ≤ H ≤ X^{1-ε}`, PROVED from `prop_2_1_58`,
which is MSTT Theorem 1.1 (iii) as printed, and the proved `lemma_1_7_weak`, by display (2.2),
page 8. -/
theorem prop_2_2_58 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H,
          ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h21⟩ := prop_2_1_58
  set g₁ : ℕ := 3
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨c, hc, C, X₀, hC⟩ := h21 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_smallS (by norm_num : (1 : ℝ) ≤ 4) (mul_pos hc hε)
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := lemma_1_7_weak hg3 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (C * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set M : ℝ := C * H * X ^ (-(c * ε))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb 0)
  have hF : Continuous (fun α => S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) :=
    (S4_continuous _ _).sub (S4sharp_cont _ _ _)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine le_trans (norm_sum_setIntegral_le (measurableSet_Ioc) Set.Ioc_subset_Icc_self _ hF _
    (fun α _ => hb α)) ?_
  rw [setIntegral_Ioc01_norm]
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g) :=
        mul_le_mul_of_nonneg_left hL hM0
    _ = C * C₂ * H * X ^ (-(c * ε)) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
        ring
    _ ≤ _ := h2

/-- Kim, Theorem 1.1 with `5/8` in place of `3/5`: `∑_{n ∈ [X,X+H]^*} d₄(n) ≪ (log X)^7
|[X,X+H]^*|` for `X^{5/8+ε} ≪ H ≪ X^{1-ε}` and `g` large. Same assembly as
`Burst4Split.kim_thm1_1_of_split`. CONDITIONAL ON `prop_2_1_58`, which is MSTT Theorem 1.1
(iii) as printed, and on Kim's `prop_3_5` and `main_term_bound`. -/
theorem kim_thm1_1_58 : D4Bound (5 / 8) 7 := by
  obtain ⟨e1, he1, h1⟩ := prop_2_2_58
  obtain ⟨e2, he2, h2⟩ := major_arcs_bound_58
  obtain ⟨e3, he3, h3⟩ := prop_2_5_58
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((5 : ℝ) / 8 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((5 : ℝ) / 8 + ε) = X ^ ((5 : ℝ) / 8 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((5 : ℝ) / 8 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

#check (kim_thm1_1_58 : D4Bound (5 / 8) 7)

#print axioms prop_2_2_58
#print axioms major_arcs_bound_58
#print axioms prop_2_5_58
#print axioms kim_thm1_1_58

end LeanLab.MissingDigit.Burst8Range58
