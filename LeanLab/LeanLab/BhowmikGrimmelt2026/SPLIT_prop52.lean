/-
Split of `prop52` of `LeanLab.BhowmikGrimmelt2026.Statements` into four leaves.

Proposition 5.2 has two parts, both for `N` and `R` with
`2 ≤ exp (sqrt (log N)) ≤ R ≤ N`.

* Part (1), under the hypothesis that no zero of a Dirichlet `L`-function of level `R` has real
  part above `1 - 1 / log R`: the sum over primitive conductors at most `R` of the interval
  maxima of `Λ(n) χ(n) - [χ = 1]` is at most `C exp (-c log N / log R)`.
* Part (2), under the hypothesis that `χ₀ mod r₀` does have such a zero `β`: the same sum, with
  the second degree term `n ^ (β - 1)` added for `χ = χ₀`, is at most
  `C (1 - β) log N exp (-c log N / log R)`; the exceptional zero shrinks the main term by the
  factor `1 - β` and by nothing more.

The two parts come with their own saving constant and their own implied constant, while a
single pair `(c, C)` has to serve both; the split therefore separates the two estimates
(leaves 1 and 2) from the bookkeeping that makes one pair serve both (leaves 3 and 4).

* LEAF 1: part (1), with its own `c > 0` and its own `C`. No count is asserted.
* LEAF 2: part (2), with its own `c > 0` and its own `C`.
* LEAF 3: the range conditions force `0 < log R` and `0 ≤ log N`, so the exponent
  `log N / log R` is nonnegative and the saving `exp (-c log N / log R)` is at most `1`.
* LEAF 4: at a fixed nonnegative exponent, lowering `c` and raising `C` keeps the bound; this
  is what lets one pair `(c, C)` serve both parts.

The assembly `prop52_split` has no sorry and does not use `prop52`. Every leaf is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 4. Part (1) of Proposition 5.2 on its own: there are `c > 0` and `C` such that,
whenever the three range conditions hold and no zero of a Dirichlet `L`-function of a primitive
conductor at most `R` has real part above `1 - 1 / log R`, the sum over the primitive conductors
at most `R` of the interval maxima of `Λ(n) χ(n) - [χ = 1]` is at most
`C exp (-c log N / log R)`. This is the character average with the exponential saving in
`log N / log R`; nothing is asserted about a zero that does exist, and the pair `(c, C)` is not
required to serve part (2) as well. Strictly weaker than `Prop52`, which also carries part (2)
with the same pair. -/
theorem leaf_no_siegel_zero_part :
    ∃ c C : ℝ, 0 < c ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R) := by
  sorry

/-- LEAF 2 of 4. Part (2) of Proposition 5.2 on its own: there are `c > 0` and `C` such that,
whenever the three range conditions hold and `χ₀ mod r₀` is a primitive real character of
conductor at most `R` with a real zero `β > 1 - 1 / log R`, `β < 1`, the sum over the primitive
conductors at most `R` of the interval maxima of `Λ(n) χ(n) - [χ = 1]`, with the second degree
term `n ^ (β - 1)` added in the archimedean place of `χ = χ₀`, is at most
`C (1 - β) log N exp (-c log N / log R)`. The factor `1 - β` is the only gain the exceptional
zero gives; the exponential saving in `log N / log R` is the same as in part (1) and the pair
`(c, C)` is again its own. Strictly weaker than `Prop52`, which also carries part (1). -/
theorem leaf_siegel_zero_part :
    ∃ c C : ℝ, 0 < c ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
        SiegelZero R r₀ χ₀ β →
      primSum R (fun r _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) ≤
        C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log R) := by
  sorry

/-- LEAF 3 of 4. The range conditions supply the signs of the two logarithms: from
`2 ≤ exp (sqrt (log N))` one gets `0 ≤ log N`, and from `exp (sqrt (log N)) ≤ R` together with
the same lower bound one gets `2 ≤ R`, hence `0 < log R`. Consequently the exponent
`log N / log R` of the saving is nonnegative, and `exp (-c log N / log R) ≤ 1` for `c > 0`.
Pure real analysis; the case `N ≤ 1` is excluded by the hypothesis, since `Real.log 0 = 0` and
`Real.log 1 = 0` give `exp 0 = 1 < 2`. -/
theorem leaf_range_logs (N : ℕ) (R : ℝ)
    (hN : 2 ≤ Real.exp (Real.sqrt (Real.log N)))
    (hR : Real.exp (Real.sqrt (Real.log N)) ≤ R) :
    0 < Real.log R ∧ 0 ≤ Real.log N := by
  have h2R : (2 : ℝ) ≤ R := le_trans hN hR
  exact ⟨Real.log_pos (by linarith), Real.log_natCast_nonneg N⟩

/-- LEAF 4 of 4. The bookkeeping that lets one pair `(c, C)` serve both parts of the
proposition: for a fixed exponent `t / s ≥ 0`, lowering the saving constant from `c₁` to
`c ≤ c₁` raises the saving to `exp (-c t / s)`, and raising the implied constant from `C` to
`C' ≥ max C 0` covers the difference; `C` itself is unrestricted in sign, which is why the
hypothesis is `C ≤ C'` with `0 ≤ C'` rather than `0 ≤ C`. Pure real analysis, no arithmetic
input. -/
theorem leaf_saving_mono {c c₁ C C' t s : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ c₁) (ht : 0 ≤ t) (hs : 0 < s)
    (hCC : C ≤ C') (hC' : 0 ≤ C') :
    C * Real.exp (-c₁ * t / s) ≤ C' * Real.exp (-c * t / s) := by
  have hexp : Real.exp (-c₁ * t / s) ≤ Real.exp (-c * t / s) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith
  have ha : 0 < Real.exp (-c₁ * t / s) := Real.exp_pos _
  have hb : 0 < Real.exp (-c * t / s) := Real.exp_pos _
  by_cases hC : 0 ≤ C
  · calc C * Real.exp (-c₁ * t / s) ≤ C' * Real.exp (-c₁ * t / s) :=
          mul_le_mul_of_nonneg_right hCC ha.le
      _ ≤ C' * Real.exp (-c * t / s) := mul_le_mul_of_nonneg_left hexp hC'
  · have h1 : C * Real.exp (-c₁ * t / s) ≤ 0 := by nlinarith
    have h2 : 0 ≤ C' * Real.exp (-c * t / s) := mul_nonneg hC' hb.le
    linarith

/-- `Prop52`, assembled from the four leaves: the two parts of the proposition at their own
pairs `(c₁, C₁)` and `(c₂, C₂)` (leaves 1 and 2), the pair `(min c₁ c₂, max C₁ C₂)` that
serves both (leaves 3 and 4), and the positivity of `1 - β` that part (2) needs to compare the
two implied constants at the same factor `(1 - β) log N`. No sorry, and `prop52` is not used. -/
theorem prop52_split : Prop52 := by
  obtain ⟨c₁, C₁, hc₁, h₁⟩ := leaf_no_siegel_zero_part
  obtain ⟨c₂, C₂, hc₂, h₂⟩ := leaf_siegel_zero_part
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max C₁ 0) (max C₂ 0), ?_⟩
  intro N R hN hR hRN
  obtain ⟨hRpos, hNpos⟩ := leaf_range_logs N R hN hR
  have hc : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hC₀ : (0 : ℝ) ≤ max (max C₁ 0) (max C₂ 0) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  constructor
  · intro hns
    refine (h₁ N R hN hR hRN hns).trans ?_
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
    refine (h₂ N R hN hR hRN r₀ χ₀ β hS).trans ?_
    calc C₂ * (1 - β) * Real.log N * Real.exp (-c₂ * Real.log N / Real.log R)
        = (C₂ * (1 - β) * Real.log N) * Real.exp (-c₂ * Real.log N / Real.log R) := by ring
      _ ≤ (max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N) *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) :=
            leaf_saving_mono hc (min_le_right c₁ c₂) hNpos hRpos hCC hC'
      _ = max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prop52_split
