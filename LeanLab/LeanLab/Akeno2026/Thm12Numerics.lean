/-
P0087 M. Akeno, arXiv 2606.29559 v1. Bookkeeping of the proof of Theorem 1.2, section 4.1
pages 31 to 32, the Appendix tables pages 36 to 37, and the numerical step of Theorem 1.3
page 35.
AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6754.
Checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here proves it.

Contents.
* `kuhnG_eq_zero`, `kuhnG_vanish_thm12`: Kuhn's `G` vanishes on the simplex once
  `1/s + (r-1)/t > 1`, the paper's reason for `T_r = 0` when `r > 10`.
  `kuhnG_pos_r10` shows the cutoff is sharp: `G > 0` somewhere on the `r = 10` simplex.
* `m4_enclosure`: the printed enclosures of `ω⁻(sθ)`, the `F`-integral and `T₅,…,T₁₀`
  give `M₄ ∈ [0.0356, 0.0400]`, hence `M₄ > 0`.
* `m4_printed_interval_not_forced`: those enclosures alone do not force the printed
  `M₄ ≥ 0.0373`; a QUESTION about outward rounding, not an error.
* `table1_*`, `table2_*`: row checks of Tables 1 and 2.
* `thm1_3_margin`: `1/12 > 1/(14 - ln(4/(1+3^{-13}))/ln 3)`.
* `thm1_2_of_prop44`: Theorem 1.2 CONDITIONAL ON Proposition 4.4, the decomposition of
  `M₄` for Kuhn's weight, and the printed numerical enclosures, all explicit hypotheses.
-/
import Mathlib
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026.Thm12Numerics
open Finset LeanLab.Akeno2026

/-! ### Kuhn's weight and the vanishing of `T_r` -/

/-- Kuhn's weight `F(u) = (1/2)·1_{u ≤ 1/t}` on `[0,1]`, extended by `0` to negative `u`. -/
noncomputable def kuhnF (t u : ℝ) : ℝ := if 0 ≤ u ∧ u ≤ 1 / t then 1 / 2 else 0

/-- `G(u₁,…,u_r) = max(0, 1 - F(u₁) - ⋯ - F(u_r))`, Appendix 5.1. -/
noncomputable def kuhnG {r : ℕ} (t : ℝ) (u : Fin r → ℝ) : ℝ :=
  max 0 (1 - ∑ i, kuhnF t (u i))

theorem kuhnF_nonneg (t u : ℝ) : 0 ≤ kuhnF t u := by
  unfold kuhnF; split_ifs <;> norm_num

/-- The support of Kuhn's weight lies in `[0, 1/t]`. -/
theorem kuhnF_support (t : ℝ) : Function.support (kuhnF t) ⊆ Set.Icc 0 (1 / t) := by
  intro u hu
  by_contra h
  apply hu
  unfold kuhnF
  rw [if_neg (fun h' => h ⟨h'.1, h'.2⟩)]

/-- If `0 < s`, `t < s`, `1/s + (r-1)/t > 1`, every `u_i ≥ 1/s` and `Σ u_i = 1`, then
`G(u) = 0`. This is the paper's reason "`T_r = 0` for `r > 10` since `1/s + (r-1)/t > 1`". -/
theorem kuhnG_eq_zero {r : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t < s)
    (hr : 1 < 1 / s + ((r : ℝ) - 1) / t) (u : Fin r → ℝ) (hu : ∀ i, 1 / s ≤ u i)
    (hsum : ∑ i, u i = 1) : kuhnG t u = 0 := by
  classical
  have hst : 1 / s < 1 / t := one_div_lt_one_div_of_lt ht hts
  have hcc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin r)))
    (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)
  simp only [Finset.card_univ, Fintype.card_fin] at hcc
  have hF : ∑ i, kuhnF t (u i) =
      ((univ.filter (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)).card : ℝ) * (1 / 2) := by
    unfold kuhnF
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, add_zero]
  unfold kuhnG
  rw [hF]
  by_cases h2 : 2 ≤ (univ.filter (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)).card
  · have : (2 : ℝ) ≤ ((univ.filter (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)).card : ℝ) := by
      exact_mod_cast h2
    exact max_eq_left (by linarith)
  · exfalso
    have hg : ∀ i, (if 0 ≤ u i ∧ u i ≤ 1 / t then 1 / s else 1 / t) ≤ u i := by
      intro i
      by_cases hi : 0 ≤ u i ∧ u i ≤ 1 / t
      · simp only [hi, and_self, if_true]; exact hu i
      · simp only [hi, if_false]
        have h0 : 0 ≤ u i := le_trans (by positivity) (hu i)
        by_contra hlt
        exact hi ⟨h0, (not_le.mp hlt).le⟩
    have hle := Finset.sum_le_sum (fun i (_ : i ∈ univ) => hg i)
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hsum] at hle
    generalize (univ.filter (fun i => 0 ≤ u i ∧ u i ≤ 1 / t)).card = c at hcc h2 hle
    generalize (univ.filter (fun i => ¬ (0 ≤ u i ∧ u i ≤ 1 / t))).card = c' at hcc hle
    have hrc : (r : ℝ) = c + c' := by rw [← hcc]; push_cast; ring
    have hc1' : (c : ℝ) ≤ 1 := by exact_mod_cast (by omega : c ≤ 1)
    have key : 1 / s + ((r : ℝ) - 1) / t ≤ (c : ℝ) * (1 / s) + (c' : ℝ) * (1 / t) := by
      rw [hrc]
      have : (c : ℝ) * (1 / s) + (c' : ℝ) * (1 / t) - (1 / s + ((c : ℝ) + c' - 1) / t)
          = (1 - c) * (1 / t - 1 / s) := by ring
      nlinarith
    linarith

/-- Proof of Theorem 1.2 parameters `s = 33.5`, `t = 9.5`: `G = 0` on the simplex for every
`r ≥ 11`, so `T_r = 0` for `r > 10`. -/
theorem kuhnG_vanish_thm12 {r : ℕ} (hr : 11 ≤ r) (u : Fin r → ℝ)
    (hu : ∀ i, 1 / (33.5 : ℝ) ≤ u i) (hsum : ∑ i, u i = 1) : kuhnG 9.5 u = 0 := by
  refine kuhnG_eq_zero (by norm_num) (by norm_num) (by norm_num) ?_ u hu hsum
  have : (11 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (10 : ℝ) / 9.5 ≤ ((r : ℝ) - 1) / 9.5 := by
    apply div_le_div_of_nonneg_right _ (by norm_num); linarith
  have h2 : (1 : ℝ) < 1 / 33.5 + 10 / 9.5 := by norm_num
  linarith

/-- The cutoff is sharp: on the `r = 10` simplex with `u_i ≥ 1/33.5` there is a point where
`G = 1/2 > 0`, so `T₁₀` is not forced to vanish, matching `T₁₀ ≈ 1.02·10⁻¹⁶ > 0`. -/
theorem kuhnG_pos_r10 : ∃ u : Fin 10 → ℝ, (∀ i, 1 / (33.5 : ℝ) ≤ u i) ∧ ∑ i, u i = 1 ∧
    kuhnG 9.5 u = 1 / 2 := by
  classical
  refine ⟨fun i => if i = 0 then 1 / 33.5 else (1 - 1 / 33.5) / 9, ?_, ?_, ?_⟩
  · intro i; dsimp only; split_ifs <;> norm_num
  · simp [Fin.sum_univ_succ]; norm_num
  · unfold kuhnG kuhnF
    simp only [Fin.sum_univ_succ, Fin.isValue]
    norm_num

/-! ### Interval arithmetic for `M₄`, page 31 to 32 -/

/-- From the printed enclosures `ω⁻(sθ) ∈ [0.56118, 0.56121]`, `∫ F ω⁺/u ∈ [0.40941, 0.40943]`
and `T₅,…,T₁₀`, with `θ = 0.1635`, `s = 33.5`, and the reduction
`M₄ = s ω⁻(sθ) - s ∫ - (2/θ) Σ_{r=5}^{10} T_r`, one gets `M₄ ∈ [0.0356, 0.0400]`. -/
theorem m4_enclosure (ω I T5 T6 T7 T8 T9 T10 : ℝ)
    (hω : 0.56118 ≤ ω ∧ ω ≤ 0.56121) (hI : 0.40941 ≤ I ∧ I ≤ 0.40943)
    (h5 : 0.3687 ≤ T5 ∧ T5 ≤ 0.3689) (h6 : 0.04192 ≤ T6 ∧ T6 ≤ 0.04193)
    (h7 : 0.001818 ≤ T7 ∧ T7 ≤ 0.001819) (h8 : 1.913e-5 ≤ T8 ∧ T8 ≤ 1.914e-5)
    (h9 : 1.327e-8 ≤ T9 ∧ T9 ≤ 1.329e-8) (h10 : 1.017e-16 ≤ T10 ∧ T10 ≤ 1.023e-16) :
    let M := 33.5 * ω - 33.5 * I - 2 / 0.1635 * (T5 + T6 + T7 + T8 + T9 + T10)
    (0.0356 : ℝ) ≤ M ∧ M ≤ 0.0400 := by
  intro M
  obtain ⟨_, _⟩ := hω; obtain ⟨_, _⟩ := hI; obtain ⟨_, _⟩ := h5; obtain ⟨_, _⟩ := h6
  obtain ⟨_, _⟩ := h7; obtain ⟨_, _⟩ := h8; obtain ⟨_, _⟩ := h9; obtain ⟨_, _⟩ := h10
  constructor <;> (simp only [M]; norm_num; linarith)

/-- The printed enclosures alone do not force the printed `M₄ ≥ 0.0373`: the corner
`ω = 0.56118`, `∫ = 0.40943` and every `T_r` at its upper end gives `M₄ < 0.0373`.
QUESTION only: the recomputed `M₄ ≈ 0.03785` lies in the printed interval. -/
theorem m4_printed_interval_not_forced :
    33.5 * (0.56118 : ℝ) - 33.5 * 0.40943 - 2 / 0.1635 *
      (0.3689 + 0.04193 + 0.001819 + 1.914e-5 + 1.329e-8 + 1.023e-16) < 0.0373 := by
  norm_num

/-! ### Rows of Tables 1 and 2, page 37 -/

/-- Table 1, Kuhn's weight, `k = 4`: `θ = 0.16328 < 1/6`, `s > 1/θ`, `t < s`, and
`1/s + 9/t < 1 < 1/s + 10/t`, so the `r`-range for `T_r` ends at `r = 10`. -/
theorem table1_kuhn_k4 :
    (0.16328 : ℝ) < 1 / 6 ∧ 1 / (0.16328 : ℝ) < 33.53 ∧ (9.56 : ℝ) < 33.53 ∧
      1 / (33.53 : ℝ) + 9 / 9.56 < 1 ∧ 1 < 1 / (33.53 : ℝ) + 10 / 9.56 := by
  norm_num

/-- Proof of Theorem 1.2: `1/s + 9/t < 1 < 1/s + 10/t` at `s = 33.5`, `t = 9.5`. -/
theorem thm12_cutoff : 1 / (33.5 : ℝ) + 9 / 9.5 < 1 ∧ 1 < 1 / (33.5 : ℝ) + 10 / 9.5 := by
  norm_num

/-- Every row of Table 1 has `s > 1/θ`, and every Kuhn row has `t < s`. -/
theorem table1_s_gt_inv_theta :
    1 / (0.50512 : ℝ) < 5.12 ∧ 1 / (0.29515 : ℝ) < 8.76 ∧ 1 / (0.18352 : ℝ) < 14.17 ∧
    1 / (0.11801 : ℝ) < 22.18 ∧ 1 / (0.07742 : ℝ) < 34.02 ∧ 1 / (0.05145 : ℝ) < 51.50 ∧
    1 / (0.47337 : ℝ) < 10.87 ∧ 1 / (0.26631 : ℝ) < 20.25 ∧ 1 / (0.16328 : ℝ) < 33.53 ∧
    1 / (0.10438 : ℝ) < 52.76 ∧ 1 / (0.06832 : ℝ) < 80.79 ∧ 1 / (0.04538 : ℝ) < 121.73 ∧
    (3.35 : ℝ) < 10.87 ∧ (5.83 : ℝ) < 20.25 ∧ (9.56 : ℝ) < 33.53 ∧ (15.08 : ℝ) < 52.76 ∧
    (23.25 : ℝ) < 80.79 ∧ (35.30 : ℝ) < 121.73 := by
  norm_num

/-- For `k = 4` only Kuhn's weight gets below `1/6`: the trivial weight row of Table 1 and
the Richert row of Table 2 sit above `1/6`. -/
theorem table_k4_vs_one_sixth :
    (1 / 6 : ℝ) < 0.18352 ∧ (1 / 6 : ℝ) < 0.16695 ∧ (0.16328 : ℝ) < 1 / 6 ∧
      (0.16328 : ℝ) < 0.1635 ∧ (0.1635 : ℝ) < 1 / 6 := by
  norm_num

/-! ### Theorem 1.3, page 35 -/

/-- `1/12 > 1/(k + 1 - ln(4/(1+3^{-k}))/ln 3)` at `k = 13`, the margin used for Theorem 1.3. -/
theorem thm1_3_margin :
    1 / (14 - Real.log (4 / (1 + (3 : ℝ)⁻¹ ^ 13)) / Real.log 3) < 1 / 12 := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < 4 / (1 + (3 : ℝ)⁻¹ ^ 13) := by positivity
  have hlt : Real.log (4 / (1 + (3 : ℝ)⁻¹ ^ 13)) < 2 * Real.log 3 := by
    rw [← Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    apply Real.log_lt_log hpos
    rw [div_lt_iff₀ (by positivity)]
    norm_num
  have hq : Real.log (4 / (1 + (3 : ℝ)⁻¹ ^ 13)) / Real.log 3 < 2 := by
    rw [div_lt_iff₀ hl3]; linarith
  apply one_div_lt_one_div_of_lt (by norm_num)
  linarith

/-! ### Theorem 1.2, CONDITIONAL -/

/-- Theorem 1.2 CONDITIONAL ON named inputs:
* `prop44`, Proposition 4.4 of the paper for a functional `Mk` and a class `PwSmooth` of
  piecewise smooth functions, both left abstract;
* `hPS`, that Kuhn's weight with `t = 9.5` is in that class;
* `hdecomp`, the reduction of `M₄` for this weight at `θ = 0.1635`, `s = 33.5` to
  `s ω⁻(sθ) - s ∫ - (2/θ) Σ_{r=5}^{10} T_r`, using symmetry of `G` for the `1/r!` and
  `T_r = 0` for `r > 10`, the latter backed by `kuhnG_vanish_thm12`;
* the printed numerical enclosures.
The support condition, `θ < 1/6` and `s > 1/θ` are proved here. -/
theorem thm1_2_of_prop44
    (Mk : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (PwSmooth : (ℝ → ℝ) → Prop)
    (prop44 : ∀ k : ℕ, 2 ≤ k → ∀ θ s : ℝ, θ < 1 / 6 → 1 / θ < s → ∀ F : ℝ → ℝ,
      PwSmooth F → (∀ u, 0 ≤ F u) →
      (∃ ε : ℝ, 0 < ε ∧ Function.support F ⊆ Set.Icc 0 (θ - ε)) →
      0 < Mk k F θ s → AlmostAllDyadic Even (DiffForm k))
    (hPS : PwSmooth (kuhnF 9.5))
    (ω I T5 T6 T7 T8 T9 T10 : ℝ)
    (hdecomp : Mk 4 (kuhnF 9.5) 0.1635 33.5 =
      33.5 * ω - 33.5 * I - 2 / 0.1635 * (T5 + T6 + T7 + T8 + T9 + T10))
    (hω : 0.56118 ≤ ω ∧ ω ≤ 0.56121) (hI : 0.40941 ≤ I ∧ I ≤ 0.40943)
    (h5 : 0.3687 ≤ T5 ∧ T5 ≤ 0.3689) (h6 : 0.04192 ≤ T6 ∧ T6 ≤ 0.04193)
    (h7 : 0.001818 ≤ T7 ∧ T7 ≤ 0.001819) (h8 : 1.913e-5 ≤ T8 ∧ T8 ≤ 1.914e-5)
    (h9 : 1.327e-8 ≤ T9 ∧ T9 ≤ 1.329e-8) (h10 : 1.017e-16 ≤ T10 ∧ T10 ≤ 1.023e-16) :
    AlmostAllDyadic Even (DiffForm 4) := by
  refine prop44 4 (by norm_num) 0.1635 33.5 (by norm_num) (by norm_num) (kuhnF 9.5) hPS
    (kuhnF_nonneg 9.5) ⟨0.1635 - 1 / 9.5, by norm_num, ?_⟩ ?_
  · refine (kuhnF_support 9.5).trans ?_
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  · rw [hdecomp]
    have := (m4_enclosure ω I T5 T6 T7 T8 T9 T10 hω hI h5 h6 h7 h8 h9 h10).1
    linarith

end LeanLab.Akeno2026.Thm12Numerics
