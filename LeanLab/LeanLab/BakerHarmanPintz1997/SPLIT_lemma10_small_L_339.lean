/-
Split of `lemma10_small_L_339` in LeanLab.BakerHarmanPintz1997.DecompJ381 into leaves.
P0069 page 24, proof of Lemma 10, the case L <= qT under (3.39). The sealed statement is
unchanged and is restated verbatim in `lemma10_small_L_339_split`.

The paper says: ||L||_4^4 << L^(3A) qT from Lemma 9, so when (3.39) holds one may replace
L^(4 - 4 sigma_3) by L^(3A) qT L^(2 - 4 sigma_3) in the proof of Lemma 4, and since
L^(3A) qT < x^(16/35) the proof goes through as before.
Leaf 1, the fourth moment ||L||_4 << L^B (qT)^(1/4): `leaf_long_fourth_moment`, shared with the
split of `lemma10_small_L_338` and imported from there. MEDIUM, CONDITIONAL ON Lemma 9.
Step 2, the range qT <= x^(0.45 - eps/2) eventually, the hypothesis (3.23) of Lemma 4, from
q <= L^A0 and T <= T1 = x^(0.45 - 2 eps/3). PROVED here as `leaf_339_qT_range`.
Leaf 3, the variant of Lemma 4 in which the fourth moment bound of the interval polynomial L,
of length at most qT, replaces (3.2) and the length condition L <= x^(8/35). HARD, it reruns the
case analysis of the proof of Lemma 4, pages 18 and 19, itself a variant of Heath-Brown and
Iwaniec, reference 12, Lemma 2.
The assembly passes the hypotheses through. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- PROVED, formerly planned as a leaf: page 24, the range condition (3.23) of Lemma 4 in the
case of Lemma 10: qT <= L^A0 x^(0.45 - 2 eps/3) <= x^(0.45 - eps/2) for x large, as x^(eps/6)
beats L^A0.
Non-vacuity: q = 1 and T = x^(0.1) for every x at least 1. -/
theorem leaf_339_qT_range :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 : ℝ) (𝒮 : ℝ → Set Cfg),
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ c.T ≤ T1 ε x) →
    ∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2) := by
  intro ε hε _ A0 𝒮 hcase
  have hs : (0 : ℝ) < ε / 6 := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop A0 hs).bound (show (0:ℝ) < 1 by norm_num)
  rw [Filter.eventually_atTop] at ho
  obtain ⟨X, hX⟩ := ho
  refine ⟨max X 1, ?_⟩
  intro x hx c hc
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hstd, hq, hT⟩ := hcase x c hc
  have hT0 : 0 ≤ c.T := by linarith [hstd.2.2.2.1]
  have hL : L x ^ A0 ≤ x ^ (ε / 6) := by
    have h := hX x hxX
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at h
    exact h
  calc (c.q : ℝ) * c.T ≤ x ^ (ε / 6) * x ^ (0.45 - 2 * ε / 3) :=
        mul_le_mul (hq.trans hL) hT hT0 (Real.rpow_nonneg hx0.le _)
    _ = x ^ (0.45 - ε / 2) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring

/-- LEAF: pages 18, 19 and 24, Lemma 4 with the fourth moment input of Lemma 10. HARD.
M, N satisfy (3.1) and (3.39) in the form max(M, N) <= x^(0.46 + eps/8), qT <= x^(0.45 - eps/2) as
in (3.23), and the third polynomial is the interval polynomial over c1 L to c2 L with L <= qT
and ||L||_4 << L^B (qT)^(1/4). The proof of Lemma 4, Cases 2 to 4, uses L only through the
large value count, where L^(4 - 4 sigma_3) is replaced by L^(3A) qT L^(2 - 4 sigma_3), and
L^(3A) qT < x^(16/35) keeps the exponents below 1/2.
Non-vacuity: Ml = Nl = x^(0.45), Ll = x^(0.1), q = 1, T = x^(0.2). -/
theorem leaf_339_lemma4_variant :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    (∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ))) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  sorry

/-- `lemma10_small_L_339`, verbatim. CONDITIONAL ON `leaf_long_fourth_moment` from the split of
`lemma10_small_L_338` and `leaf_339_lemma4_variant`; `leaf_339_qT_range` is proved. -/
theorem lemma10_small_L_339_split :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  obtain ⟨ε1, hε1, hvar⟩ := leaf_339_lemma4_variant
  refine ⟨min (1 / 100) ε1, lt_min (by norm_num) hε1, ?_⟩
  intro ε hε hεlt A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hcase h339 hsmall
  have hε0 : ε < 1 / 100 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεv : ε < ε1 := lt_of_lt_of_le hεlt (min_le_right _ _)
  exact hvar ε hε hεv B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod
    (fun x c hc => (hcase x c hc).1)
    (leaf_339_qT_range ε hε hε0 A0 𝒮
      (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1, (hcase x c hc).2.2.2.1⟩))
    h339 hsmall
    (leaf_long_fourth_moment ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall)

#print axioms leaf_339_qT_range
#print axioms lemma10_small_L_339_split

end LeanLab.BakerHarmanPintz1997
