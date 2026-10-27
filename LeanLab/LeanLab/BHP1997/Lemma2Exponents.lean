/-
P0069 Baker, Harman, Pintz 1997, Lemma 2, page 15, and its applications on pages 16, 17 and 46,
read from the page images papers/P0069-original.pdf. Unit U-5061, CLOUD 20261019T0213Z-cloud14.

Exponents in units of `log M`: `Q = M^h`, `qT = M^κ` with `κ ≤ γ`, `V = M^v` with
`v ≤ h/2` from (3.2), since `|Q| = |M|^h ≪ M^{h/2} ℒ^{-A}`. The target is `M^{β/2}`, that is
`Q^{β/2h}`.
PROVED: the first term of (3.20) when `β ≥ 2h`; the second term under (3.21); the bound from
(3.22) under `(qT)⁴ ≤ M^{2h+β}`; that (3.18) gives `(qT)⁴ ≤ M^{2h+β-ε}`; and that every
application of Lemma 2 in the chapter has `2h ≤ β < 6h - ε`.
QUESTION, not a finding: (3.19) allows `2h - ε < β < 2h`, but there the step
`QV^{(β-2h)/h} ≤ Q(Qℒ^{-A₃})^{(β-2h)/2h}` reverses, `first_term_reverses`, and (3.22) raises an
upper bound for `V` to a negative power. The printed proof covers `β ≥ 2h` only. Harmless:
no application uses `β < 2h`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma2

/-- First term of (3.20): `Q V^{(β-2h)/h} ≤ Q^{β/2h}` when `β ≥ 2h` and `V ≤ Q^{1/2}`. -/
theorem first_term {h β v : ℝ} (hh : 0 < h) (hβ : 2 * h ≤ β) (hv : v ≤ h / 2) :
    h + v * ((β - 2 * h) / h) ≤ β / 2 := by
  have h1 : 0 ≤ (β - 2 * h) / h := div_nonneg (by linarith) hh.le
  have := mul_le_mul_of_nonneg_right hv h1
  have e : h / 2 * ((β - 2 * h) / h) = β / 2 - h := by field_simp
  linarith

/-- QUESTION: for `β < 2h` the same step fails at every `V < Q^{1/2}`. -/
theorem first_term_reverses {h β v : ℝ} (hh : 0 < h) (hβ : β < 2 * h) (hv : v < h / 2) :
    β / 2 < h + v * ((β - 2 * h) / h) := by
  have h1 : (β - 2 * h) / h < 0 := div_neg_of_neg_of_pos (by linarith) hh
  have := mul_lt_mul_of_neg_right hv h1
  have e : h / 2 * ((β - 2 * h) / h) = β / 2 - h := by field_simp
  linarith

/-- Second term of (3.20) under (3.21): if `V ≥ (qT Q^{(2h-β)/2h})^{h/(6h-β)}`, then
`qT Q V^{-4 + (β-2h)/h} ≤ Q^{β/2h}`. -/
theorem second_term {h β κ v : ℝ} (hh : 0 < h) (hβ6 : β < 6 * h)
    (h321 : (κ + h - β / 2) * h / (6 * h - β) ≤ v) :
    κ + h + v * (-4 + (β - 2 * h) / h) ≤ β / 2 := by
  have h6 : 0 < 6 * h - β := by linarith
  have e : -4 + (β - 2 * h) / h = -((6 * h - β) / h) := by field_simp; ring
  rw [e]
  have h2 : 0 < (6 * h - β) / h := div_pos h6 hh
  have := mul_le_mul_of_nonneg_right h321 h2.le
  have e2 : (κ + h - β / 2) * h / (6 * h - β) * ((6 * h - β) / h) = κ + h - β / 2 := by
    have : h * 6 - β ≠ 0 := ne_of_gt (by linarith)
    field_simp
  linarith

/-- (3.22): if (3.21) fails, `V^{(β-2h)/h} |S| V² ≪ (qT Q^{(2h-β)/2h})^{(β-2h)/(6h-β)} (Q + qT)`,
and this is `≪ Q^{β/2h}` once `(qT)⁴ ≤ M^{2h+β}`, `2h ≤ β < 6h`. Here `max h κ` is `Q + qT`. -/
theorem third_term {h β κ v : ℝ} (hh : 0 < h) (hβ : 2 * h ≤ β) (hβ6 : β < 6 * h)
    (hv : v ≤ (κ + h - β / 2) * h / (6 * h - β)) (h4 : 4 * κ ≤ β + 2 * h) :
    v * ((β - 2 * h) / h) + max h κ ≤ β / 2 := by
  have h6 : 0 < 6 * h - β := by linarith
  have h1 : 0 ≤ (β - 2 * h) / h := div_nonneg (by linarith) hh.le
  have := mul_le_mul_of_nonneg_right hv h1
  have e : (κ + h - β / 2) * h / (6 * h - β) * ((β - 2 * h) / h) =
      (κ + h - β / 2) * (β - 2 * h) / (6 * h - β) := by field_simp
  rw [e] at this
  have key : (κ + h - β / 2) * (β - 2 * h) / (6 * h - β) + max h κ ≤ β / 2 := by
    rw [← sub_nonneg]
    have hb : β / 2 - ((κ + h - β / 2) * (β - 2 * h) / (6 * h - β) + max h κ) =
        ((β / 2 - max h κ) * (6 * h - β) - (κ + h - β / 2) * (β - 2 * h)) / (6 * h - β) := by
      have : h * 6 - β ≠ 0 := ne_of_gt (by linarith)
      field_simp; ring
    rw [hb]
    apply div_nonneg _ h6.le
    rcases le_total κ h with hk | hk
    · rw [max_eq_left hk]
      nlinarith [mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℝ) ≤ β - 2 * h)]
    · rw [max_eq_right hk]
      nlinarith
  linarith

/-- "a consequence of (3.18)": `β ≥ 4γ - 2h + ε` and `qT ≤ M^γ` give `(qT)⁴ ≤ M^{2h+β-ε}`. -/
theorem of_eq318 {h β γ κ ε : ℝ} (h318 : 4 * γ - 2 * h + ε ≤ β) (hκ : κ ≤ γ) :
    4 * κ ≤ 2 * h + β - ε := by linarith

/-- Every application of Lemma 2 has `2h ≤ β < 6h - ε`, for `ε < 1`: pages 16 (i), (ii), (iii),
β = 8, 12, 6 with h = 3, 3, 2; page 17 Case (b), `L` with `h = 2`, `β = 4γ - 4 + ε`,
`γ = 0.45/α₁`, `0.18 < α₁ < 0.225`; `N` with `h = 3`, `β = 1.8/α₂ - 6 + ε`, `0.1 < α₂ < 0.15`;
page 46, Lemma 32, `h = 1`, `β = τ = 2β'/(β' - 2)` with `β' = 2(h' + a) ≥ 8`. -/
theorem applications {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (2 * 3 ≤ (8 : ℝ) ∧ (8 : ℝ) < 6 * 3 - ε) ∧ (2 * 3 ≤ (12 : ℝ) ∧ (12 : ℝ) < 6 * 3 - ε) ∧
    (2 * 2 ≤ (6 : ℝ) ∧ (6 : ℝ) < 6 * 2 - ε) ∧
    (∀ α₁ : ℝ, 0.18 < α₁ → α₁ < 0.225 →
      2 * 2 ≤ 4 * (0.45 / α₁) - 4 + ε ∧ 4 * (0.45 / α₁) - 4 + ε < 6 * 2 - ε) ∧
    (∀ α₂ : ℝ, 0.1 < α₂ → α₂ < 0.15 →
      2 * 3 ≤ 1.8 / α₂ - 6 + ε ∧ 1.8 / α₂ - 6 + ε < 6 * 3 - ε) ∧
    (∀ β' : ℝ, 8 ≤ β' → 2 * 1 ≤ 2 * β' / (β' - 2) ∧ 2 * β' / (β' - 2) < 6 * 1 - ε) := by
  refine ⟨⟨by norm_num, by linarith⟩, ⟨by norm_num, by linarith⟩, ⟨by norm_num, by linarith⟩,
    ?_, ?_, ?_⟩
  · intro α₁ h1 h2
    have hp : 0 < α₁ := by linarith
    have a1 : 0.45 / α₁ ≥ 2 := by rw [ge_iff_le, le_div_iff₀ hp]; linarith
    have a2 : 0.45 / α₁ < 2.5 := by rw [div_lt_iff₀ hp]; linarith
    constructor <;> linarith
  · intro α₂ h1 h2
    have hp : 0 < α₂ := by linarith
    have a1 : 1.8 / α₂ ≥ 12 := by rw [ge_iff_le, le_div_iff₀ hp]; linarith
    have a2 : 1.8 / α₂ < 18 := by rw [div_lt_iff₀ hp]; linarith
    constructor <;> linarith
  · intro β' h
    have hp : 0 < β' - 2 := by linarith
    constructor
    · rw [le_div_iff₀ hp]; linarith
    · have : 2 * β' / (β' - 2) ≤ 8 / 3 := by rw [div_le_div_iff₀ hp (by norm_num)]; linarith
      linarith

end LeanLab.BHP1997.Lemma2
