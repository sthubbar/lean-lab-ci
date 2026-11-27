/-
ROUTE BURST S10, burst-20261124, step prop81mergedb. The minor arc leaf `leaf_minor_count_S10`
of Prop81MergedS10.lean, page 31 of P0029, Bhowmik and Grimmelt 2026, asks for one `ε₀` fixed
before every `ε`. Lemma 4.2 of page 16, proved as `lemma42` of Minor84.lean, gives by Chebyshev
only a threshold `X^{1-ε/4}` that depends on `ε`, as `minor_count_eps_S10` of
Prop81MinorEpsS10.lean. This file proves, without sorry and unconditionally:

* `leaf_minor_count_swapped_S10`: the page 31 sentence with the quantifiers `∀ ε ∃ ε₀`, the
  exact bound `Cε (X^{1+ε}/X^ϑ + X^{3/5+ε})` of `leaf_minor_count_S10`.
* `minor_count_fixed_S10`: for a fixed `ε₀`, the count is at most `C X^{3/5+4ε₀}`, which is
  what Chebyshev on Lemma 4.2 gives with the threshold fixed; it does not reach `X^{3/5+ε}` for
  `ε < 4ε₀`.

and the assembly `prop81_swapped_S10`, Proposition 8.1 display 8.3 with `ε₀` chosen after `ε`,
CONDITIONAL only on `leaf_major_formula_S10`, the cited Pintz input of LEAF 1. No new sorry,
no new definitions.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Prop81MergedS10
import LeanLab.BhowmikGrimmelt2026.Prop81MinorEpsS10

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- Page 31 with Lemma 4.2, p. 16: for each fixed `ε₀ > 0` the minor arc part exceeds
`X^{1-ε₀}` for at most `C X^{3/5+4ε₀}` even `N ≤ X`, at `R = X^ϑ`. PROVED from `lemma42`. -/
theorem minor_count_fixed_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε₀ : ℝ)
    (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε₀))).card : ℕ) : ℝ) ≤
        C * X ^ (3 / 5 + 4 * ε₀) := by
  obtain ⟨C, hC⟩ := minor_count_eps_S10 ϑ hϑ hϑ' (4 * ε₀) (by linarith)
  refine ⟨C, fun X hX => ?_⟩
  have := hC X hX
  rwa [show 1 - 4 * ε₀ / 4 = 1 - ε₀ by ring] at this

/-- The page 31 sentence "By Lemma 4.2 ... `|r_𝔪(N)| ≤ X^{1−ε₀}` for all even `N ≤ X` with at
most `O_ε(X^{1+ε}/R + X^{3/5+ε})` exceptions", `R = X^ϑ`, with `ε₀ = ε/4` chosen after `ε`.
PROVED from `lemma42`; the order `∃ ε₀ ∀ ε` of `leaf_minor_count_S10` is the open QUESTION. -/
theorem leaf_minor_count_swapped_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) :
    ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Cε : ℝ, ∀ X : ℝ, 2 ≤ X →
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖rMinor ⌊X⌋₊ (X ^ ϑ) N‖ ≤ X ^ (1 - ε₀))).card : ℕ) : ℝ) ≤
        Cε * (X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := minor_count_eps_S10 ϑ hϑ hϑ' ε hε
  refine ⟨ε / 4, by linarith, |C|, fun X hX => ?_⟩
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : 0 ≤ X ^ (1 + ε) / X ^ ϑ := by positivity
  have h2 : 0 ≤ X ^ (3 / 5 + ε) := by positivity
  calc _ ≤ C * X ^ (3 / 5 + ε) := hC X hX
    _ ≤ |C| * X ^ (3 / 5 + ε) := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |C| * (X ^ (1 + ε) / X ^ ϑ + X ^ (3 / 5 + ε)) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- Proposition 8.1, display 8.3, pp. 30 to 31, exactly as `Prop81` of Statements.lean except
that `ε₀` is chosen after `ε`; `h`, `c'` and `C` stay before `ε`. CONDITIONAL only on
`leaf_major_formula_S10`, LEAF 1, cited Pintz [20, Thm 1]; the minor arc side is PROVED. -/
theorem prop81_swapped_S10 (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) :
    ∃ h c' C : ℝ, 0 < h ∧ 0 < c' ∧
    ∀ ε : ℝ, 0 < ε → ∃ ε₀ Cε : ℝ, 0 < ε₀ ∧ ∀ X : ℝ, 2 ≤ X →
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ), χ.IsPrimitive → IsRealChar χ →
      (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < h / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      ((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => Even N ∧
          ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            C * (singular N * X * (δ * Real.log X) ^ c' +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 + X ^ (1 - ε₀)))).card : ℕ) : ℝ) ≤
        Cε * X ^ (3 / 5 + ε) := by
  obtain ⟨h, c', ε₁, C₁, hh, hc', hε₁, hmaj⟩ := leaf_major_formula_S10 ϑ hϑ hϑ'
  refine ⟨h, c', |C₁| + 1, hh, hc', ?_⟩
  intro ε hε
  obtain ⟨ε₂, hε₂, Cε, hCε⟩ := leaf_minor_count_swapped_S10 ϑ hϑ hϑ' ε hε
  refine ⟨min ε₁ ε₂, 2 * |Cε|, lt_min hε₁ hε₂, ?_⟩
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

#print axioms LeanLab.BhowmikGrimmelt2026.minor_count_fixed_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_minor_count_swapped_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prop81_swapped_S10
