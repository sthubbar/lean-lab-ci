/-
U-1707, BhowmikGrimmelt2026, P0029 Proposition 5.2 restated against its source,
run 20261121T0803Z-27066.

The lab transcription `Prop52` of Proposition 5.2, P0029 page 18, allows `R` up to `N`, as
printed. It is refuted at `R = N` by `not_prop52_dq4` in DQ4Decisions.lean. The source the
paper cites, Gallagher 1970, Invent. Math. 11, Theorem 7 on page 337 display (29), proves its
estimate only in the range `exp (sqrt (log x)) ≤ Q ≤ x ^ b` with a small absolute `b > 0`.
The paper itself applies the proposition only at `R = N ^ δ` with `δ` sufficiently small,
page 18 after the statement.

DECISION: `Prop52Corrected` keeps both parts of the printed proposition word for word and
replaces the upper end `R ≤ N` by Gallagher's `R ≤ N ^ b`, with `b > 0` an absolute constant
chosen together with `c` and `C`. It is a CITED named hypothesis, never PROVED. Consumers that
took `h52 : Prop52` must be restated with `h52 : Prop52Corrected` and use it only at levels
`R ≤ N ^ b`.

Checks proved here, no open step:
* `prop52Corrected_of_prop52`: the old statement implies the new one at `b = 1`, so the
  correction only narrows the range.
* `prop52Corrected_range_nonempty`: for every `b > 0` the range of `R` is nonempty for some
  `N`, so the statement is not vacuously true.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- Proposition 5.2, P0029 page 18, parts (1) and (2), with the range of `R` cut to
Gallagher 1970 Theorem 7, page 337: `2 ≤ exp (sqrt (log N)) ≤ R ≤ N ^ b`. CITED. -/
noncomputable def Prop52Corrected : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, ∀ N : ℕ, ∀ R : ℝ,
    2 ≤ Real.exp (Real.sqrt (Real.log N)) → Real.exp (Real.sqrt (Real.log N)) ≤ R →
    R ≤ (N : ℝ) ^ b →
    ((¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ), SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R)) ∧
    (∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ), SiegelZero R r₀ χ₀ β →
      primSum R (fun r _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) ≤
        C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log R))

/-- The printed statement implies the corrected one with `b = 1`. PROVED. Since `Prop52` is
false this is vacuous; it records that the correction only narrows the range of `R`. -/
theorem prop52Corrected_of_prop52 (h : Prop52) : Prop52Corrected := by
  obtain ⟨c, hc, C, hC⟩ := h
  refine ⟨c, hc, 1, one_pos, C, ?_⟩
  intro N R h2 hR hRN
  rw [Real.rpow_one] at hRN
  exact hC N R h2 hR hRN

/-- Vacuity instance: for every `b > 0` there are `N` and `R` in the corrected range.
PROVED. -/
theorem prop52Corrected_range_nonempty (b : ℝ) (hb : 0 < b) :
    ∃ N : ℕ, ∃ R : ℝ, 2 ≤ Real.exp (Real.sqrt (Real.log N)) ∧
      Real.exp (Real.sqrt (Real.log N)) ≤ R ∧ R ≤ (N : ℝ) ^ b := by
  set M : ℝ := Real.exp (1 / b ^ 2 + 1) with hM
  have hMpos : 0 < M := Real.exp_pos _
  refine ⟨⌈M⌉₊, Real.exp (Real.sqrt (Real.log ⌈M⌉₊)), ?_, le_rfl, ?_⟩
  all_goals
    have hNM : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
    have hNpos : (0 : ℝ) < ⌈M⌉₊ := lt_of_lt_of_le hMpos hNM
    have hL : 1 / b ^ 2 + 1 ≤ Real.log ⌈M⌉₊ := by
      rw [← Real.log_exp (1 / b ^ 2 + 1)]
      exact Real.log_le_log (Real.exp_pos _) hNM
    have hb2 : 0 < 1 / b ^ 2 := by positivity
    have hL1 : 1 ≤ Real.log ⌈M⌉₊ := by linarith
  · have hs : 1 ≤ Real.sqrt (Real.log ⌈M⌉₊) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hL1
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    exact h1.trans (Real.exp_le_exp.mpr hs)
  · rw [Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    set L := Real.log ⌈M⌉₊ with hLdef
    have hL0 : 0 ≤ L := by linarith
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
    have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    -- b * sqrt L ≥ 1, since L ≥ 1 / b ^ 2
    have hbs : 1 ≤ b * Real.sqrt L := by
      have h1 : (1 / b) ^ 2 ≤ L := by
        have : (1 / b) ^ 2 = 1 / b ^ 2 := by ring
        linarith
      have h2 : 1 / b ≤ Real.sqrt L := by
        have := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by positivity)] at this
      have h3 : b * (1 / b) = 1 := by field_simp
      nlinarith
    nlinarith

end LeanLab.BhowmikGrimmelt2026
