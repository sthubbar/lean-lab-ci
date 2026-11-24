/-
Split of `leaf_long_fourth_moment` in LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338.
P0069 page 24, ||L||_4^4 << L^(3A) qT for L <= qT, from Lemma 9.
Leaf 1, the fourth power bound, CONDITIONAL ON Lemma 9. MEDIUM.
The assembly takes the fourth root, PROVED here from the leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- LEAF: page 24, ||L||_4^4 << L^B qT for the interval L <= qT, from Lemma 9 via
`Reflection425.interval_fourth_moment_of_lemma9`, `principal_polar_fourth_sum_le` and
|S| <= q (2T + 1) for a well spaced set. MEDIUM, CONDITIONAL ON Lemma 9 as hypothesis.
Non-vacuity: q = 1, T = x^(0.1), L = x^(0.05), S the points t = T/2 + k. -/
theorem leaf_lfm_fourth_power (h9 : Lemma9) :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 c1 c2 : ℝ) (Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    ∃ B K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ^ 4 ≤ K * (L x ^ B * (c.q * c.T)) := by
  sorry

/-- `leaf_long_fourth_moment`, verbatim, CONDITIONAL ON `leaf_lfm_fourth_power`
with the cited `lemma9`. -/
theorem leaf_long_fourth_moment_split :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 c1 c2 : ℝ) (Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ)) := by
  intro ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall
  obtain ⟨B, K, X0, hK, h⟩ :=
    leaf_lfm_fourth_power lemma9 ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall
  refine ⟨B / 4, K ^ (1 / 4 : ℝ), max X0 1, Real.rpow_nonneg hK _, ?_⟩
  intro x hx c hc
  have hx0 : X0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hLx : 0 ≤ L x := Real.log_nonneg hx1
  have hstd := (hcase x c hc).1
  have hq : (0 : ℝ) ≤ c.q := Nat.cast_nonneg _
  have hT : 0 ≤ c.T := by linarith [hstd.2.2.2.1]
  have hp := split338_pnorm_nonneg (longDP c1 c2 (Ll x)) c 4
  have h4 := h x hx0 c hc
  have hLB : 0 ≤ L x ^ B := Real.rpow_nonneg hLx _
  have hqT : 0 ≤ (c.q : ℝ) * c.T := mul_nonneg hq hT
  calc pnorm (longDP c1 c2 (Ll x)) c 4
      = (pnorm (longDP c1 c2 (Ll x)) c 4 ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp]; norm_num
    _ ≤ (K * (L x ^ B * (c.q * c.T))) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = K ^ (1 / 4 : ℝ) * (L x ^ (B / 4) * (c.q * c.T) ^ (1 / 4 : ℝ)) := by
        rw [Real.mul_rpow hK (mul_nonneg hLB hqT), Real.mul_rpow hLB hqT,
          ← Real.rpow_mul hLx]
        ring_nf

/-- `leaf_long_fourth_moment`, verbatim, as `leaf_long_fourth_moment_proof`.
Same content as `leaf_long_fourth_moment_split`. -/
theorem leaf_long_fourth_moment_proof :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 c1 c2 : ℝ) (Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ)) :=
  leaf_long_fourth_moment_split

end LeanLab.BakerHarmanPintz1997

#print axioms LeanLab.BakerHarmanPintz1997.leaf_long_fourth_moment_split
#print axioms LeanLab.BakerHarmanPintz1997.leaf_long_fourth_moment_proof
