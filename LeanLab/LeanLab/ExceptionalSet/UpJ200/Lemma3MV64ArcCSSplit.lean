import LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit

/-!
# Split of the LEAF `mv64t_arc_cs` of `Lemma3MV64TildeSplit`

Burst burst-20261122, Claude cloud session S112, step mv64t_arc_cs_split.

Source P0015, Montgomery and Vaughan 1975, journal pages 361 to 364, displays (6.1), (6.4̃),
(6.6), (6.6̃), (6.7), (6.7̃). The split mirrors the non exceptional split in
`Lemma2MV/Remainder66Split.lean`, where `rem66_expand_64`, `rem66_cs_second` and
`rem66_cs_third` give the arc bound.

* DEFINITIONS: `WchiExc`, the exceptional `W(ψ,η)` with `S(χ̃χ₀,η) = T̃(η) + W(χ̃χ₀,η)`;
  `arcSecond`, `arcSecondT`, `arcThird`, the three remainder terms of the expanded square (6.4̃).
* LEAF `arc_expand_64t`, HARD: (6.1) and (6.4̃), the exact expansion.
* LEAF `arc_cs_second`, MEDIUM: Cauchy Schwarz with (6.7), giving the first sum of (6.6).
* LEAF `arc_cs_secondT`, MEDIUM: Cauchy Schwarz with (6.7̃), giving the new sum of (6.6̃).
* LEAF `arc_cs_third`, MEDIUM: Cauchy Schwarz, giving the second sum of (6.6).
* PROVED from these: `mv64t_arc_cs_of_leaves`, type checked equal to
  `type_of% @Lemma3MV64TildeSplit.mv64t_arc_cs`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV64ArcCSSplit

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
  (T Wchi mainWeight arcIntegral rem66_cchi rem66_arcSum)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral (excWeight crossWeight arcTt arcTTt)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit (A2exc A3exc A4exc A2exc_nonneg)

open Classical in
/-- P0015 page 361: the exceptional `W(ψ,η)` for `ψ` of modulus `q`. When `r̃ ∣ q` and
`ψ = χ̃χ₀`, it is `S(χ̃χ₀,η) - T̃(η)`; otherwise it is the `W(ψ,η)` of (6.3), the lab's `Wchi`. -/
noncomputable def WchiExc {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) {q : ℕ}
    (ψ : DirichletCharacter ℂ q) (η : ℝ) : ℂ :=
  if h : r ∣ q then
    (if ψ = DirichletCharacter.changeLevel h χ then Wchi P X ψ η - Ttilde β P X η
      else Wchi P X ψ η)
  else Wchi P X ψ η

/-- P0015 (6.4̃), the terms `2 T(η) W(ψ,η)`:
`2 μ(q) φ(q)⁻² Σ_ψ c_ψ(-n) τ(ψ̄) ∫ T(η) W(ψ,η) e(-nη) dη` with the exceptional `W`. -/
noncomputable def arcSecond {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  2 * ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((q.totient : ℂ) ^ 2) *
    ∑ᶠ ψ : DirichletCharacter ℂ q, rem66_cchi ψ (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1 *
      ∫ η in (-(P / (q * X)))..(P / (q * X)), T P X η * WchiExc β P X χ ψ η * eC (-(η * n))

/-- P0015 (6.4̃), the terms `2 T̃(η) W(ψ,η)`, present only when `r̃ ∣ q`:
`2 τ(χ̄̃χ₀) φ(q)⁻² Σ_ψ c_{χ̃χ₀ψ}(-n) τ(ψ̄) ∫ T̃(η) W(ψ,η) e(-nη) dη`. -/
noncomputable def arcSecondT {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  if h : r ∣ q then
    2 * rem66_cchi (DirichletCharacter.changeLevel h χ)⁻¹ 1 / ((q.totient : ℂ) ^ 2) *
      ∑ᶠ ψ : DirichletCharacter ℂ q,
        rem66_cchi (DirichletCharacter.changeLevel h χ * ψ) (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1 *
          ∫ η in (-(P / (q * X)))..(P / (q * X)),
            Ttilde β P X η * WchiExc β P X χ ψ η * eC (-(η * n))
  else 0

/-- P0015 (6.4̃), the terms `W(ψ,η) W(ψ',η)`:
`φ(q)⁻² Σ_{ψ,ψ'} c_{ψψ'}(-n) τ(ψ̄) τ(ψ̄') ∫ W(ψ,η) W(ψ',η) e(-nη) dη` with the exceptional `W`. -/
noncomputable def arcThird {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (q n : ℕ) : ℂ :=
  1 / ((q.totient : ℂ) ^ 2) *
    ∑ᶠ ψ : DirichletCharacter ℂ q, ∑ᶠ ψ' : DirichletCharacter ℂ q,
      rem66_cchi (ψ * ψ') (-(n : ℤ)) * rem66_cchi ψ⁻¹ 1 * rem66_cchi ψ'⁻¹ 1 *
        ∫ η in (-(P / (q * X)))..(P / (q * X)),
          WchiExc β P X χ ψ η * WchiExc β P X χ ψ' η * eC (-(η * n))

/-- LEAF: P0015 displays (6.1) and (6.4̃), pages 361 and 362, class HARD. Expand `S(a/q+η)` by
the characters mod `q`, (6.1), write `S(χ₀,η) = T(η) + W(χ₀,η)`, and when `r̃ ∣ q` also
`S(χ̃χ₀,η) = T̃(η) + W(χ̃χ₀,η)`, square, sum over the reduced residues `a` and integrate: the
arc sum is the three main terms plus the three remainder terms of (6.4̃). Mirrors the proved
`Lemma2MVSplit.rem66_expand_64`. -/
theorem arc_expand_64t (P X β : ℝ) (hP : 0 ≤ P) (hX : 0 < X) (hPX : 2 * P ≤ X) (hβ : β ≤ 1)
    (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hne : χ ≠ 1) (hr1 : 1 ≤ r) (hrP : (r : ℝ) ≤ P)
    (q : ℕ) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ P) (n : ℕ) (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ X) :
    rem66_arcSum P X q n =
      (mainWeight q n * arcIntegral P X q n + excWeight χ q n * arcTt β P X q n +
        2 * crossWeight χ q n * arcTTt β P X q n) +
      (arcSecond β P X χ q n + arcSecondT β P X χ q n + arcThird β P X χ q n) := by
  sorry

/-- LEAF: P0015 displays (6.6) and (6.7), page 362, first sum, class MEDIUM. Cauchy Schwarz on
each integral `∫ T(η) W(ψ,η) e(-nη) dη`, with `∫|T|² ≪ X`, (6.7), the proved
`Lemma2MVSplit.rem66_T_L2`, and `W(ψ,η) = W(ψ*,η)` on the shorter interval, the exceptional
`W(χ̃)` when `ψ* = χ̃`. Mirrors the proved `Lemma2MVSplit.rem66_cs_second`. -/
theorem arc_cs_second : ∃ C : ℝ, 0 < C ∧
    ∀ P X β : ℝ, 0 ≤ P → 0 < X → 2 * P ≤ X → β ≤ 1 →
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcSecond β P X χ q n‖ ≤ C * (Real.sqrt X * A2exc β P X χ q n) := by
  sorry

/-- LEAF: P0015 displays (6.6̃) and (6.7̃), page 362, class MEDIUM. Cauchy Schwarz on each
integral `∫ T̃(η) W(ψ,η) e(-nη) dη`, with `∫|T̃|² ≤ Σ_{n≤X} n^{2β-2} ≤ X` for `β ≤ 1`, (6.7̃),
and `W(ψ,η) = W(ψ*,η)` on the shorter interval. -/
theorem arc_cs_secondT : ∃ C : ℝ, 0 < C ∧
    ∀ P X β : ℝ, 0 ≤ P → 0 < X → 2 * P ≤ X → β ≤ 1 →
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcSecondT β P X χ q n‖ ≤ C * (Real.sqrt X * A4exc β P X χ q n) := by
  sorry

/-- LEAF: P0015 display (6.6), page 362, second sum, class MEDIUM. Cauchy Schwarz on each
integral `∫ W(ψ,η) W(ψ',η) e(-nη) dη` and `W(ψ,η) = W(ψ*,η)` on the shorter interval, with the
exceptional `W(χ̃)`. Mirrors the proved `Lemma2MVSplit.rem66_cs_third`. -/
theorem arc_cs_third :
    ∀ P X β : ℝ, 0 ≤ P → 0 < X → 2 * P ≤ X → β ≤ 1 →
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖arcThird β P X χ q n‖ ≤ A3exc β P X χ q n := by
  sorry

/-- PROVED from the four leaves: the exact type twin of `Lemma3MV64TildeSplit.mv64t_arc_cs`,
by the triangle inequality on the three remainder terms. -/
theorem mv64t_arc_cs_of_leaves : ∃ C : ℝ, 0 < C ∧
    ∀ P X β : ℝ, 0 ≤ P → 0 < X → 2 * P ≤ X → β ≤ 1 →
    ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 ≤ r → (r : ℝ) ≤ P →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ P → ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ X →
        ‖rem66_arcSum P X q n -
            (mainWeight q n * arcIntegral P X q n + excWeight χ q n * arcTt β P X q n +
              2 * crossWeight χ q n * arcTTt β P X q n)‖ ≤
          C * (Real.sqrt X * (A2exc β P X χ q n + A4exc β P X χ q n) + A3exc β P X χ q n) := by
  obtain ⟨C2, hC2, h2⟩ := arc_cs_second
  obtain ⟨C4, hC4, h4⟩ := arc_cs_secondT
  refine ⟨C2 + C4 + 1, by positivity, ?_⟩
  intro P X β hP hX hPX hβ r hNZ χ hprim hsq hne hr1 hrP q hq hqP n hn hnX
  have e := arc_expand_64t P X β hP hX hPX hβ r χ hprim hsq hne hr1 hrP q hq hqP n hn hnX
  have b2 := h2 P X β hP hX hPX hβ r hNZ χ hprim hsq hne hr1 hrP q hq hqP n hn hnX
  have b4 := h4 P X β hP hX hPX hβ r hNZ χ hprim hsq hne hr1 hrP q hq hqP n hn hnX
  have b3 := arc_cs_third P X β hP hX hPX hβ r hNZ χ hprim hsq hne hr1 hrP q hq hqP n hn hnX
  rw [e, add_sub_cancel_left]
  have hA2 := A2exc_nonneg β P X χ q n
  have hA3 : 0 ≤ A3exc β P X χ q n := le_trans (norm_nonneg _) b3
  have hA4 : 0 ≤ C4 * (Real.sqrt X * A4exc β P X χ q n) := le_trans (norm_nonneg _) b4
  have hsX := Real.sqrt_nonneg X
  have hA4' : 0 ≤ Real.sqrt X * A4exc β P X χ q n := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_pos_of_neg hC4 hc
    linarith
  have hS2 : 0 ≤ Real.sqrt X * A2exc β P X χ q n := mul_nonneg hsX hA2
  calc ‖arcSecond β P X χ q n + arcSecondT β P X χ q n + arcThird β P X χ q n‖
      ≤ ‖arcSecond β P X χ q n‖ + ‖arcSecondT β P X χ q n‖ + ‖arcThird β P X χ q n‖ :=
        norm_add₃_le
    _ ≤ C2 * (Real.sqrt X * A2exc β P X χ q n) + C4 * (Real.sqrt X * A4exc β P X χ q n) +
        A3exc β P X χ q n := by linarith
    _ ≤ (C2 + C4 + 1) * (Real.sqrt X * (A2exc β P X χ q n + A4exc β P X χ q n) +
        A3exc β P X χ q n) := by
        rw [mul_add (Real.sqrt X)]
        nlinarith [mul_nonneg hC2.le hA4', mul_nonneg hC4.le hS2, mul_nonneg hC2.le hA3,
          mul_nonneg hC4.le hA3]

example : type_of% @mv64t_arc_cs_of_leaves =
    type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma3MV64TildeSplit.mv64t_arc_cs := rfl

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV64ArcCSSplit
