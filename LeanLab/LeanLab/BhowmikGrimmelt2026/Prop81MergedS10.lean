/-
ROUTE BURST S10, burst-20261124, step prop81merged. A faithful re split of `Prop81`,
Proposition 8.1 of P0029, Bhowmik and Grimmelt 2026, pages 30 and 31, display 8.3.

The earlier split SPLIT_prop81.lean separates the two main terms, and its second leaf was shown
in Prop81SecondSiegelAllS10.lean, branch claude/BhowmikGrimmelt2026-prop81second, to force the
absence of Landau Siegel zeros. This file follows the paper's own sketch instead, page 30 to 31:

* LEAF 1, `leaf_major_formula_S10`, HARD, CITED Pintz [20, Thm 1]: the major arc part `r_M(N)`
  of display 4.4 equals `𝔖(N) N + 𝔖(χ̃,χ̃,N) B(β̃,β̃) N^{2β̃-1}` up to the three errors of
  display 8.3, for every even `N` of the window. Both main terms stay together; this is the only
  place where the zero enters.
* LEAF 2, `leaf_minor_count_S10`, HARD: the sentence of page 31, "By Lemma 4.2, or [20, (5.3)],
  we have `|r_m(N)| ≤ X^{1-ε₀}` for all even `N ≤ X` with at most `O_ε(X^{1+ε}/R + X^{3/5+ε})`
  exceptions", with `R = X^ϑ`.
* PROVED, `r2_major_minor_S10`: display 4.4, `r₂(N) = r_M(N) + r_m(N)` for `N ≤ X`, from
  display 4.2 as `r2_eq_integral150` of MeanSquareCore150.lean.
* PROVED, `prop81_merged_S10`: `Prop81` exactly as in Statements.lean from the two leaves, by the
  triangle inequality, `ε₀ = min`, and `X^{1+ε}/X^ϑ ≤ X^{3/5+ε}` for `ϑ ≥ 2/5`.

New definition: `rMajorS10`, the major arc integral of display 4.4, the complement of `rMinor`
of Minor84.lean. The length of `S` is `⌊X⌋`, as `rMinor` takes a natural length.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements
import LeanLab.BhowmikGrimmelt2026.Minor84
import LeanLab.BhowmikGrimmelt2026.MeanSquareCore150
import LeanLab.BhowmikGrimmelt2026.Decomp150a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- `r_𝔐(N) = ∫_{𝔐(R)} S(α)² e(−Nα) dα`, display 4.4, p. 14, the major arc part, with `S` of
length `X` and the major arcs `𝔐(R)` of display 4.3 as `MajorArc` of Minor84.lean. -/
noncomputable def rMajorS10 (X : ℕ) (R : ℝ) (N : ℕ) : ℂ :=
  ∫ α in Set.Ico (0 : ℝ) 1,
    Set.indicator {α | MajorArc X R α} (fun α => Ssum X α ^ 2 * ee (-(N * α))) α

/-- Display 4.4, p. 14: `r₂(N) = r_𝔐(N) + r_𝔪(N)` for `N ≤ X`. Proved from display 4.2. -/
theorem r2_major_minor_S10 {X N : ℕ} (hN : N ≤ X) (R : ℝ) :
    (r2 N : ℂ) = rMajorS10 X R N + rMinor X R N := by
  set f : ℝ → ℂ := fun α => Ssum X α ^ 2 * ee (-(N * α)) with hf
  have hcont : Continuous f := by
    rw [hf]
    exact ((continuous_Ssum150 X).pow 2).mul
      (continuous_ee150.comp (by fun_prop))
  have hint : IntegrableOn f (Set.Ico (0 : ℝ) 1) :=
    (hcont.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  have hA : MeasurableSet {α : ℝ | MajorArc X R α} := measurableSet_majorArc84 X R
  have hsplit : ∀ α, f α = Set.indicator {α | MajorArc X R α} f α +
      Set.indicator {α | ¬ MajorArc X R α} f α := by
    intro α
    by_cases h : MajorArc X R α
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have h1 : IntegrableOn (Set.indicator {α | MajorArc X R α} f) (Set.Ico (0 : ℝ) 1) :=
    hint.indicator hA
  have h2 : IntegrableOn (Set.indicator {α | ¬ MajorArc X R α} f) (Set.Ico (0 : ℝ) 1) :=
    hint.indicator hA.compl
  rw [← r2_eq_integral150 hN, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Ico_eq_integral_Ioc]
  unfold rMajorS10 rMinor
  rw [← integral_add h1 h2]
  exact setIntegral_congr_fun measurableSet_Ico (fun α _ => hsplit α)

/-- LEAF: Proposition 8.1 sketch, major arcs, p. 30, the explicit formula of Pintz [20, Thm 1]
with the cutoff `H = H₁` of display 8.2. Class HARD, CITED Pintz [20, Thm 1, Lem. 4.9,
(2.8), §8 to §9], P0016. For `2/5 ≤ ϑ < 4/9`, `R = X^ϑ`, `𝓛 = log X`, a primitive real `χ̃`
modulo `r̃ ≤ R` with a zero `β̃ = 1 − δ̃`, `0 < δ̃ < h/𝓛`, the four pairs from `ϱ₀ = 1` and
`β̃` give, for every even `N ∈ [X/2, X]`,
`r_𝔐(N) = 𝔖(N)N + 𝔖(χ̃,χ̃,N)B(β̃,β̃)N^{2β̃−1}
  + O(𝔖(N)X(δ̃𝓛)^{c₁}) + O(𝔖(N)N r̃/φ(r̃)²) + O(X^{1−ε₀})`,
the major arc half of display 8.3; the constants depend only on `ϑ`, as on p. 30. -/
theorem leaf_major_formula_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ h c' ε₀ C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < ε₀ ∧
      ∀ X : ℝ, 2 ≤ X →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ), χ.IsPrimitive → IsRealChar χ →
      (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < h / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      ∀ N ∈ Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊, Even N →
        ‖rMajorS10 ⌊X⌋₊ (X ^ ϑ) N - singular N * N -
            genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
              (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
          C * (singular N * X * (δ * Real.log X) ^ c' +
            singular N * N * r / (Nat.totient r : ℝ) ^ 2 + X ^ (1 - ε₀)) := by
  sorry

/-- LEAF: Proposition 8.1 sketch, minor arcs, p. 31, the sentence "By Lemma 4.2, or [20, (5.3)],
we have `|r_𝔪(N)| ≤ X^{1−ε₀}` (after decreasing `ε₀` if necessary) for all even `N ≤ X` with
at most `O_ε(X^{1+ε}/R + X^{3/5+ε})` exceptions", at `R = X^ϑ`, `2/5 ≤ ϑ < 4/9`. Class HARD:
as printed `ε₀` is fixed before `ε`, while Chebyshev on Lemma 4.2, proved as `lemma42` of
Minor84.lean, gives only `X^{3/5+2ε₀}(log X)^9`; see the QUESTION in the note. -/
theorem leaf_minor_count_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε₀))).card : ℕ) : ℝ) ≤
        Cε * (X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε)) := by
  sorry

/-- Mechanical, p. 31: the first term `X^{1+ε}/R` with `R = X^ϑ` is dominated by `X^{3/5+ε}`
precisely when `ϑ ≥ 2/5`; here the direction used, for `X ≥ 1`. -/
theorem minor_term_dominated_S10 {X ϑ ε : ℝ} (hX : 1 ≤ X) (hϑ : 2 / 5 ≤ ϑ) :
    X ^ (1 + ε) / X ^ ϑ ≤ X ^ (3 / 5 + ε) := by
  have hX0 : 0 < X := by linarith
  rw [← Real.rpow_sub hX0]
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- `Prop81` exactly as in Statements.lean, assembled from LEAF 1, LEAF 2 and display 4.4. With
`ε₀ = min(ε₁, ε₂)` and `C = |C₁| + 1`: off the minor arc exceptions, the triangle inequality on
`r₂ = r_𝔐 + r_𝔪` bounds the deviation, using `𝔖(N) ≥ 1` for even `N` from Decomp150a.lean. No
sorry here; `prop81` is not used. -/
theorem prop81_merged_S10 : Prop81 := by
  intro ϑ hϑ hϑ'
  obtain ⟨h, c', ε₁, C₁, hh, hc', hε₁, hmaj⟩ := leaf_major_formula_S10 ϑ hϑ hϑ'
  obtain ⟨ε₂, hε₂, hmin⟩ := leaf_minor_count_S10 ϑ hϑ hϑ'
  refine ⟨h, c', min ε₁ ε₂, |C₁| + 1, hh, hc', lt_min hε₁ hε₂, ?_⟩
  intro ε hε
  obtain ⟨Cε, hCε⟩ := hmin ε hε
  refine ⟨2 * |Cε|, ?_⟩
  intro X hX r _inst χ δ hprim hreal hr hδ0 hδL hL
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  set W := Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊
  have hsub : (W.filter (fun N => Even N ∧
        ¬ ‖(r2 N : ℂ) - singular N * N -
            genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
              (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
          (|C₁| + 1) * (singular N * X * (δ * Real.log X) ^ c' +
            singular N * N * r / (Nat.totient r : ℝ) ^ 2 + X ^ (1 - min ε₁ ε₂)))) ⊆
      (Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε₂)) := by
    intro N hN
    rw [Finset.mem_filter] at hN ⊢
    obtain ⟨hNW, hEv, hbad⟩ := hN
    have hNW' := Finset.mem_Icc.mp hNW
    have hc1 : 1 ≤ ⌈X / 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
    refine ⟨Finset.mem_Icc.mpr ⟨hc1.trans hNW'.1, hNW'.2⟩, hEv, ?_⟩
    intro hm
    apply hbad
    have hNpos : 0 < N := by omega
    have hS : (1 : ℝ) ≤ singular N := singular_ge_one461 N hEv hNpos
    have hdec := r2_major_minor_S10 hNW'.2 (X ^ ϑ)
    have hM := hmaj X hX r χ δ hprim hreal hr hδ0 hδL hL N hNW hEv
    set E : ℝ := singular N * X * (δ * Real.log X) ^ c' +
      singular N * N * r / (Nat.totient r : ℝ) ^ 2 with hEdef
    have hE : 0 ≤ E := by
      have : 0 ≤ (δ * Real.log X) ^ c' := Real.rpow_nonneg (by positivity) _
      have : 0 ≤ singular N * X * (δ * Real.log X) ^ c' := by positivity
      have : 0 ≤ singular N * N * r / (Nat.totient r : ℝ) ^ 2 := by positivity
      linarith
    have hp1 : X ^ (1 - ε₁) ≤ X ^ (1 - min ε₁ ε₂) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [min_le_left ε₁ ε₂])
    have hp2 : X ^ (1 - ε₂) ≤ X ^ (1 - min ε₁ ε₂) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith [min_le_right ε₁ ε₂])
    have hP0 : 0 ≤ X ^ (1 - ε₁) := Real.rpow_nonneg hX0.le _
    have hCabs : C₁ * (E + X ^ (1 - ε₁)) ≤ |C₁| * (E + X ^ (1 - min ε₁ ε₂)) := by
      calc C₁ * (E + X ^ (1 - ε₁)) ≤ |C₁| * (E + X ^ (1 - ε₁)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ |C₁| * (E + X ^ (1 - min ε₁ ε₂)) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    rw [hdec]
    calc ‖rMajorS10 ⌊X⌋₊ (X ^ ϑ) N + rMinor ⌊X⌋₊ (X ^ ϑ) N - singular N * N -
            genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
              (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖
        = ‖(rMajorS10 ⌊X⌋₊ (X ^ ϑ) N - singular N * N -
            genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
              (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)) + rMinor ⌊X⌋₊ (X ^ ϑ) N‖ := by
          congr 1; ring
      _ ≤ _ := norm_add_le _ _
      _ ≤ C₁ * (E + X ^ (1 - ε₁)) + X ^ (1 - ε₂) := by
          have := hM
          rw [show singular N * X * (δ * Real.log X) ^ c' +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 + X ^ (1 - ε₁) =
              E + X ^ (1 - ε₁) by rw [hEdef]] at this
          linarith
      _ ≤ (|C₁| + 1) * (E + X ^ (1 - min ε₁ ε₂)) := by nlinarith
  have hcard := Finset.card_le_card hsub
  have hb := hCε X hX
  have hdom := minor_term_dominated_S10 (ε := ε) hX1 hϑ
  have hA0 : 0 ≤ X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε) := by positivity
  calc (((W.filter _).card : ℕ) : ℝ) ≤ (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε₂))).card : ℝ) := by exact_mod_cast hcard
    _ ≤ Cε * (X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε)) := hb
    _ ≤ |Cε| * (X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hA0
    _ ≤ |Cε| * (X ^ (3 / 5 + ε) + X ^ (3 / 5 + ε)) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = 2 * |Cε| * X ^ (3 / 5 + ε) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.r2_major_minor_S10
#print axioms LeanLab.BhowmikGrimmelt2026.minor_term_dominated_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prop81_merged_S10
