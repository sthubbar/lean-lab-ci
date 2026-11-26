/-
Split of `Prop52Corrected` of Prop52Corrected1707.lean into two LEAF pieces, route burst
burst-20261124, session S10, step prop52siegelb.

`Prop52`, Proposition 5.2 of P0029 page 18 as printed with `R ≤ N`, is refuted by
`not_prop52_dq4`, and the two leaves of SPLIT_prop52.lean are false as a pair by
`not_both_leaves_S10` in Prop52SiegelS10.lean. The defect is the printed upper end `R ≤ N`; the
normalisation `1 / (|I| + N/R)` is transcribed faithfully. `Prop52Corrected` keeps both parts
word for word with Gallagher's range `R ≤ N ^ b`, Gallagher 1970 Theorem 7, page 337 display
(29). This file splits it the same way SPLIT_prop52.lean split `Prop52`:

* LEAF `leaf_corrected_no_siegel_S10`, HARD: part (1) in the corrected range, with its own
  `c`, `b` and `C`.
* LEAF `leaf_corrected_siegel_S10`, HARD: part (2) in the corrected range, with its own
  `c`, `b` and `C`.
* Assembly `prop52Corrected_split_S10`, no sorry: one triple `(min c₁ c₂, min b₁ b₂, C)` serves
  both parts, by the proved `leaf_range_logs` and `leaf_saving_mono` of SPLIT_prop52.lean and the
  monotonicity of `N ^ b` in `b` for `N ≥ 1`.

Neither leaf is refuted by the one point interval of `not_prop52_dq4`: at `R ≤ N ^ b` with
`b < 1` the one point value is `log p / (N / R)`, at most `N ^ (b - 1) log N`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_prop52
import LeanLab.BhowmikGrimmelt2026.Prop52Corrected1707

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- LEAF: Proposition 5.2 part (1), P0029 page 18 first display, in the range of Gallagher 1970
Theorem 7, page 337 display (29). Class HARD, a citation wall: Gallagher's prime number theorem
for primitive characters, from the log free zero density estimate and the zero free region.
There are `c > 0`, `b > 0` and `C` such that, whenever `2 ≤ exp (sqrt (log N)) ≤ R ≤ N ^ b` and
there is no Siegel zero of level `R`, the sum over primitive characters of conductor at most `R`
of the interval maxima of `Λ(n) χ(n) - [χ = 1]`, weighted by `1 / (|I| + N/R)`, is at most
`C exp (-c log N / log R)`. -/
theorem leaf_corrected_no_siegel_S10 :
    ∃ c b C : ℝ, 0 < c ∧ 0 < b ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ (N : ℝ) ^ b →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R) := by
  sorry

/-- LEAF: Proposition 5.2 part (2), P0029 page 18 second display, in the range of Gallagher 1970
Theorem 7, page 337 display (29), with the Deuring Heilbronn factor of Gallagher's Theorem 7
for an exceptional zero. Class HARD, a citation wall. There are `c > 0`, `b > 0` and `C` such
that, whenever `2 ≤ exp (sqrt (log N)) ≤ R ≤ N ^ b` and `χ₀ mod r₀` is a primitive real
character of conductor at most `R` with a zero `β` in `(1 - 1 / log R, 1)`, the same sum with
the term `n ^ (β - 1)` added for `χ = χ₀` is at most `C (1 - β) log N exp (-c log N / log R)`. -/
theorem leaf_corrected_siegel_S10 :
    ∃ c b C : ℝ, 0 < c ∧ 0 < b ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ (N : ℝ) ^ b →
      ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
        SiegelZero R r₀ χ₀ β →
      primSum R (fun r _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) ≤
        C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log R) := by
  sorry

/-- For `N ≥ 1` the level `N ^ b` grows with `b`, so `R ≤ N ^ (min b₁ b₂)` gives
`R ≤ N ^ b₁` and `R ≤ N ^ b₂`. PROVED. -/
theorem level_min_S10 {N : ℕ} {R b₁ b₂ : ℝ} (hN : 1 ≤ (N : ℝ))
    (hR : R ≤ (N : ℝ) ^ (min b₁ b₂)) : R ≤ (N : ℝ) ^ b₁ ∧ R ≤ (N : ℝ) ^ b₂ :=
  ⟨hR.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_left _ _)),
   hR.trans (Real.rpow_le_rpow_of_exponent_le hN (min_le_right _ _))⟩

/-- The range condition `2 ≤ exp (sqrt (log N))` forces `1 ≤ N`. PROVED. -/
theorem one_le_N_of_range_S10 {N : ℕ} (hN : 2 ≤ Real.exp (Real.sqrt (Real.log N))) :
    (1 : ℝ) ≤ N := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp at hN
  · exact_mod_cast h0

/-- `Prop52Corrected`, assembled from the two LEAF pieces and the proved bookkeeping lemmas
`leaf_range_logs` and `leaf_saving_mono` of SPLIT_prop52.lean. No sorry in this proof. -/
theorem prop52Corrected_split_S10 : Prop52Corrected := by
  obtain ⟨c₁, b₁, C₁, hc₁, hb₁, h₁⟩ := leaf_corrected_no_siegel_S10
  obtain ⟨c₂, b₂, C₂, hc₂, hb₂, h₂⟩ := leaf_corrected_siegel_S10
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, min b₁ b₂, lt_min hb₁ hb₂,
    max (max C₁ 0) (max C₂ 0), ?_⟩
  intro N R hN hR hRN
  obtain ⟨hRN₁, hRN₂⟩ := level_min_S10 (one_le_N_of_range_S10 hN) hRN
  obtain ⟨hRpos, hNpos⟩ := leaf_range_logs N R hN hR
  have hc : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hC₀ : (0 : ℝ) ≤ max (max C₁ 0) (max C₂ 0) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  constructor
  · intro hns
    refine (h₁ N R hN hR hRN₁ hns).trans ?_
    exact leaf_saving_mono hc (min_le_left c₁ c₂) hNpos hRpos
      (le_trans (le_max_left C₁ 0) (le_max_left (max C₁ 0) (max C₂ 0))) hC₀
  · intro r₀ _inst χ₀ β hS
    have hβ : β < 1 := hS.2.2.2.2.1
    have h1β : (0 : ℝ) < 1 - β := by linarith
    have hfac : (0 : ℝ) ≤ (1 - β) * Real.log N := mul_nonneg h1β.le hNpos
    have hC₂ : C₂ ≤ max (max C₁ 0) (max C₂ 0) :=
      le_trans (le_max_left C₂ 0) (le_max_right (max C₁ 0) (max C₂ 0))
    have hCC : C₂ * (1 - β) * Real.log N ≤ max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N := by
      calc C₂ * (1 - β) * Real.log N = C₂ * ((1 - β) * Real.log N) := by ring
        _ ≤ max (max C₁ 0) (max C₂ 0) * ((1 - β) * Real.log N) :=
              mul_le_mul_of_nonneg_right hC₂ hfac
        _ = max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N := by ring
    have hC' : (0 : ℝ) ≤ max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N :=
      mul_nonneg (mul_nonneg hC₀ h1β.le) hNpos
    refine (h₂ N R hN hR hRN₂ r₀ χ₀ β hS).trans ?_
    calc C₂ * (1 - β) * Real.log N * Real.exp (-c₂ * Real.log N / Real.log R)
        = (C₂ * (1 - β) * Real.log N) * Real.exp (-c₂ * Real.log N / Real.log R) := by ring
      _ ≤ (max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N) *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) :=
            leaf_saving_mono hc (min_le_right c₁ c₂) hNpos hRpos hCC hC'
      _ = max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.level_min_S10
#print axioms LeanLab.BhowmikGrimmelt2026.one_le_N_of_range_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prop52Corrected_split_S10
