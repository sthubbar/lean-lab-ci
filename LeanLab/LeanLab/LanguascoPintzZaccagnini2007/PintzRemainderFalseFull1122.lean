import LeanLab.LanguascoPintzZaccagnini2007.PintzRemainderFalse1122

/-!
FALSIFY follow up for `leaf_remainder_bound481` of `SPLIT_pintz_explicit_formula481`,
CLOUD S101 burst-20261122.

`PintzRemainderFalse1122` showed that the skeleton with the committed constants
`c = ε₀ = B = 1`, `Cε = 1`, `X₀ = 1` cannot be closed. This file frees all four constants:
for EVERY `c > 0`, every `ε₀`, every `B`, and every `Cε`, the remainder estimate of the leaf
already fails at the single scale `X = 2`, uniformly over the `H ≥ H₀`, `T ≥ T₀`. Hence any
witness of `leaf_remainder_bound481` must take `X₀ (H, T) > 2` for some `H` and `T`, and the
full statement of the leaf with the extra restriction `X₀ ≤ 2` is false.

What is NOT proved here: the negation of the leaf with a free threshold `X₀`. That would need
`binaryMajor131 X n P` to depend on the admissible `P` by more than `o (X)` at arbitrarily large
`X` for the pole only family, or the existence of exceptional zeros in box (8) at arbitrarily large
`X`; both are analytic statements far beyond the explicit computation at `X = 2`.

Witness, as in the sibling file: the pole only family `K = 0`, `Sg = 𝔖(n)`, `X = n = 2`, and the
two endpoints `2^(2/5) < 2^(41/100)` of the admissible range, where the major arc integrals
`(log 2)^2 sin (2 π P) / (2 π)` differ.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real MeasureTheory
open scoped Classical

noncomputable section

/-- For every choice of the constants `c > 0`, `ε₀`, `B`, `Cε` of `leaf_remainder_bound481`, its
remainder estimate fails at the scale `X = 2` for some `H ≥ H₀` and `T ≥ T₀`. -/
theorem leaf_remainder_bound481_fails_at_two (H₀ T₀ c ε₀ B : ℝ) (Cε : ℝ → ℕ) (hc : 0 < c) :
    ¬ (∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
          ∀ P : ℝ, AdmissibleP131 2 P →
          ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
            (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
            (z 0).1 = 1 → (z 0).2.2 = 1 →
            (∀ i, i ≠ 0 → z i ∈ zeroBox481 2 H T P) →
            (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
              analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
            (∀ n ∈ evenJ131 2, Sg 0 0 n = (Sing n : ℂ)) →
            (∀ i j n, n ∈ evenJ131 2 → ‖Sg i j n‖ ≤ Sing n) →
            (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 2 →
              (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) →
            ∀ n ∈ evenJ131 2,
              |binaryMajor131 2 n P -
                (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                  gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
                B * (((2 : ℕ) : ℝ) * Real.exp (-c * H) + ((2 : ℕ) : ℝ) / Real.sqrt T)) := by
  intro h
  set P₁ : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 5) with hP₁
  set P₂ : ℝ := (2 : ℝ) ^ ((41 : ℝ) / 100) with hP₂
  have hadm1 : AdmissibleP131 2 P₁ := by
    refine ⟨by rw [hP₁]; norm_num, ?_⟩
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hadm2 : AdmissibleP131 2 P₂ := by
    refine ⟨?_, by rw [hP₂]; norm_num⟩
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hn : (2 : ℕ) ∈ evenJ131 2 := by
    unfold evenJ131
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by norm_num, le_refl 2⟩, by decide, by norm_num⟩
  let z : Fin (0 + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ :=
    fun _ => ⟨1, ((1 : DirichletCharacter ℂ 1), (1 : ℂ))⟩
  let Sg : Fin (0 + 1) → Fin (0 + 1) → ℕ → ℂ := fun _ _ n => (Sing n : ℂ)
  have hbox : ∀ (H T P : ℝ) (i : Fin (0 + 1)), i ≠ 0 → z i ∈ zeroBox481 2 H T P := by
    intro H T P i hi
    exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)) hi
  have hmult : ∀ w, ((univ.filter (fun i : Fin (0 + 1) => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
      analyticOrderNatAt (Lfun481 w.2.1) w.2.2 := by
    intro w
    have hcard : (univ.filter (fun i : Fin (0 + 1) => i ≠ 0 ∧ z i = w)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_iff_forall_notMem.2 ?_
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      exact hi.1 (Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega))
    rw [hcard]
    exact Nat.zero_le _
  have hSgb : ∀ i j n, n ∈ evenJ131 2 → ‖Sg i j n‖ ≤ Sing n := by
    intro i j n _
    simp only [Sg, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (Sing_nonneg131 n))
  have hSge : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 2 →
      (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε := by
    intro ε _ _ i j n _ hd
    rcases hd with hd | hd <;> exact absurd (one_dvd _) hd
  have key : ∀ a b c e : ℝ, |a - c| ≤ e → |b - c| ≤ e → |a - b| ≤ 2 * e := by
    intro a b c e h1 h2
    have := abs_sub_le a c b
    rw [abs_sub_comm c b] at this
    linarith
  have hbound : ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      |binaryMajor131 2 2 P₁ - binaryMajor131 2 2 P₂| ≤
        2 * (B * (2 * Real.exp (-c * H) + 2 / Real.sqrt T)) := by
    intro H T hH hT
    have e1 := h H T hH hT P₁ hadm1 0 z Sg rfl rfl (hbox H T P₁) hmult
      (fun n _ => rfl) hSgb hSge 2 hn
    have e2 := h H T hH hT P₂ hadm2 0 z Sg rfl rfl (hbox H T P₂) hmult
      (fun n _ => rfl) hSgb hSge 2 hn
    have e3 := key _ _ _ _ e1 e2
    simp only [Nat.cast_ofNat] at e3
    exact e3
  have hne := binaryMajor131_two_two_ne
  set δ : ℝ := |binaryMajor131 2 2 P₁ - binaryMajor131 2 2 P₂| with hδ
  have hδpos : 0 < δ := abs_pos.2 (sub_ne_zero.2 hne)
  -- the bound at `H = H₀` already forces `0 ≤ B`
  have hB0 : 0 ≤ B := by
    have hb := hbound H₀ T₀ le_rfl le_rfl
    by_contra hneg
    push_neg at hneg
    have hpos : 0 ≤ 2 * Real.exp (-c * H₀) + 2 / Real.sqrt T₀ := by positivity
    have : 2 * (B * (2 * Real.exp (-c * H₀) + 2 / Real.sqrt T₀)) ≤ 0 := by
      have := mul_nonpos_of_nonpos_of_nonneg hneg.le hpos
      linarith
    linarith
  set M : ℝ := 8 * (B + 1) / δ with hM
  have hMpos : 0 < M := by positivity
  set H : ℝ := max H₀ (Real.log M / c) with hHdef
  set T : ℝ := max T₀ ((M + 1) ^ 2) with hTdef
  have hb := hbound H T (le_max_left _ _) (le_max_left _ _)
  have hexp : Real.exp (-c * H) ≤ 1 / M := by
    have hH : Real.log M / c ≤ H := le_max_right _ _
    have hcH : Real.log M ≤ c * H := by
      rw [div_le_iff₀ hc] at hH; linarith
    have : Real.exp (-c * H) ≤ Real.exp (-Real.log M) :=
      Real.exp_le_exp.2 (by linarith)
    refine le_trans this (le_of_eq ?_)
    rw [Real.exp_neg, Real.exp_log hMpos, one_div]
  have hsqrt : 2 / Real.sqrt T ≤ 2 / M := by
    have hT : (M + 1) ^ 2 ≤ T := le_max_right _ _
    have hs : M + 1 ≤ Real.sqrt T :=
      calc M + 1 = Real.sqrt ((M + 1) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hT
    exact div_le_div_of_nonneg_left (by norm_num) hMpos (by linarith)
  have hsum : 2 * Real.exp (-c * H) + 2 / Real.sqrt T ≤ 4 / M := by
    have := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)
    have h4 : 2 * (1 / M) + 2 / M = 4 / M := by ring
    linarith
  have hfin : 2 * (B * (2 * Real.exp (-c * H) + 2 / Real.sqrt T)) ≤ 2 * (B * (4 / M)) := by
    have := mul_le_mul_of_nonneg_left hsum hB0
    linarith
  have hval : 2 * (B * (4 / M)) = δ * (B / (B + 1)) := by
    rw [hM]
    field_simp
    ring
  have hlt : δ * (B / (B + 1)) < δ := by
    have : B / (B + 1) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    nlinarith
  linarith

/-- The full statement of `leaf_remainder_bound481` with the threshold restricted to `X₀ ≤ 2` is
false, for every `H₀` and `T₀`. -/
theorem leaf_remainder_bound481_small_threshold_false (H₀ T₀ : ℝ) :
    ¬ (∃ c ε₀ B : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
      ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
        ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
          ∃ X₀ : ℕ, X₀ ≤ 2 ∧ ∀ X : ℕ, X₀ ≤ X →
            ∀ P : ℝ, AdmissibleP131 X P →
            ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
              (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
              (z 0).1 = 1 → (z 0).2.2 = 1 →
              (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) →
              (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
                analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
              (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) →
              (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) →
              (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenJ131 X →
                (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) →
              ∀ n ∈ evenJ131 X,
                |binaryMajor131 X n P -
                  (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                    gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
                  B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)) := by
  rintro ⟨c, ε₀, B, hc, -, -, Cε, -, h⟩
  apply leaf_remainder_bound481_fails_at_two H₀ T₀ c ε₀ B Cε hc
  intro H T hH hT
  obtain ⟨X₀, hX₀2, hX⟩ := h H T hH hT
  exact hX 2 hX₀2

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.leaf_remainder_bound481_fails_at_two
#print axioms LeanLab.LPZ2007.leaf_remainder_bound481_small_threshold_false
