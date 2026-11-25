/-
P0069 page 24, proof of Lemma 10, the case L <= qT under (3.39): a faithful replacement for the
leaf `leaf_339_lemma4_variant`, which `leaf_339_lemma4_variant_false` refutes as stated because it
drops the principal height condition of the parent. The new leaf keeps T0 <= T and
T/2 <= abs t <= T for principal points. `lemma10_small_L_339_split_p5` restates
`lemma10_small_L_339_split` verbatim and proves it from the new leaf, the proved
`leaf_339_qT_range` and `leaf_long_fourth_moment`.
Non-vacuity of the leaf: Ml = Nl = x^(0.45), Ll = x^(0.1), q = 1, T = x^(0.2), principal
points at heights in [T/2, T]. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_339_p4_false

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- Proved sanity check: the counterexample configuration `p4Cfg` of
`leaf_339_lemma4_variant_false` violates the principal height condition of the new leaf, for
every x > 0, since its principal point sits at t = 0 while T = x^0.4 > 0. -/
theorem p5_sanity (x : ℝ) (hx : 0 < x) :
    ¬ (∀ e ∈ (p4Cfg x).S, e.2 = 1 → (p4Cfg x).T / 2 ≤ |e.1| ∧ |e.1| ≤ (p4Cfg x).T) := by
  intro h
  have h1 := (h ((0 : ℝ), (1 : DirichletCharacter ℂ 1)) (Finset.mem_singleton_self _) rfl).1
  have hT : 0 < (p4Cfg x).T := Real.rpow_pos_of_pos hx _
  rw [show |((0 : ℝ), (1 : DirichletCharacter ℂ 1)).1| = 0 from abs_zero] at h1
  linarith

/-- LEAF: pages 18, 19 and 24, Lemma 4 with the fourth moment input of Lemma 10, faithful form. HARD.
The refuted leaf plus T0 <= T and T/2 <= abs t <= T at principal points, from the parent.
Page 24: replace L^(4 - 4 sigma_3) by L^(3A) qT L^(2 - 4 sigma_3) in the proof of Lemma 4,
pages 18 and 19. QUESTION: Case 1 of Theorem 4, followed by Lemma 4, uses the sup bound (3.2)
for L, which the interval polynomial need not satisfy; whether Case 1 goes through is open.
The refuting family fails the height condition, `p5_sanity`. -/
theorem leaf_339_lemma4_variant_p5 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ T0 x ≤ c.T ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    (∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ))) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  sorry

/-- `lemma10_small_L_339`, verbatim, as `lemma10_small_L_339_split`. CONDITIONAL ON
`leaf_339_lemma4_variant_p5` and `leaf_long_fourth_moment`; `leaf_339_qT_range` is proved. -/
theorem lemma10_small_L_339_split_p5 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  obtain ⟨ε1, hε1, hvar⟩ := leaf_339_lemma4_variant_p5
  refine ⟨min (1 / 100) ε1, lt_min (by norm_num) hε1, ?_⟩
  intro ε hε hεlt A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hcase h339 hsmall
  have hε0 : ε < 1 / 100 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεv : ε < ε1 := lt_of_lt_of_le hεlt (min_le_right _ _)
  exact hvar ε hε hεv B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod
    (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.2.1, (hcase x c hc).2.2.2.2⟩)
    (leaf_339_qT_range ε hε hε0 A0 𝒮
      (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1, (hcase x c hc).2.2.2.1⟩))
    h339 hsmall
    (leaf_long_fourth_moment ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall)

#print axioms p5_sanity
#print axioms lemma10_small_L_339_split_p5

end LeanLab.BakerHarmanPintz1997
