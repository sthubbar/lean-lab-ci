/-
P0069 Baker, Harman, Pintz 1997, Lemma 35 and (5.16), pages 50 and 51, read from the page images
papers/P0069-original.pdf. Unit U-5093, CLOUD 20261019T0213Z-cloud14.

Exponents of `Y`; `c₁ = (1 + 7θ₂)/15 - ε`, `c₂ = (36θ₂ - 2)/11 - ε`, `c₃ = (1 + 22θ₂)/60 - 2ε`.
PROVED: Lemma 35 on `Q₁`, the grouping `(p₁p₂, p₃)` lands in Lemma 33's `P₁`:
`-θ₂ + ε ≤ 4(β₁ + β₂) + 3β₃ - 2 ≤ θ₂ - ε` from `β₃ ≤ β₂`, `4β₁ + 7β₂ ≤ 2 + θ₂ - ε` and
`β₁ + β₂ ≥ 1/2 - (θ₂ + 3c₁)/4 + ε`, with `β₃ ≤ c₂`. And (5.16): `c₁ - 4c₃ = -θ₂ + 7ε`, the lower
end of `P₂` exactly at `ε = 0`, `c1_sub_4c3`, which is how `c₃` is chosen; the upper end
`-θ₂ + 8ε + 1/6 + c₃/3 < θ₂ - ε`, from `β₃ < 1/6 + c₃/3` on `D`. All MATCH. `Q₂`, U-5153: the lower end of `P₂` holds, `Q2_low`; the upper end
fails on a strip of width `(1 - 8θ₂)/15` as printed, `Q2_high_fails`, FINDING F-5023 cosmetic; repaired by
`2 + θ₂ - ε` for `2 + c₁`, `Q2_repair`.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma35

/-- Lemma 35, `Q₁`. -/
theorem Q1_in_P1 {b1 b2 b3 th2 c1 ε : ℝ} (hε : 0 ≤ ε) (h32 : b3 ≤ b2) (hc1 : c1 ≤ b3)
    (hq1 : 4 * b1 + 7 * b2 ≤ 2 + th2 - ε) (hq2 : 1 / 2 - (th2 + 3 * c1) / 4 + ε ≤ b1 + b2) :
    4 * (b1 + b2) + 3 * b3 - 2 ≤ th2 - ε ∧ -th2 + ε ≤ 4 * (b1 + b2) + 3 * b3 - 2 := by
  constructor <;> linarith

/-- On `Q₁`, `β₃ ≤ β₂ ≤ (2 + θ₂)/11 < c₂` for the paper's `θ₂`. -/
theorem Q1_b3_le_c2 {b1 b2 ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 0.001) (h21 : b2 ≤ b1)
    (hq1 : 4 * b1 + 7 * b2 ≤ 2 + 2 * (1 / 16 - 1 / 10 ^ 5)) :
    b2 ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε := by
  norm_num at hq1 ⊢
  linarith

/-- `c₁ - 4c₃ = -θ₂ + 7ε`. -/
theorem c1_sub_4c3 (th2 ε : ℝ) :
    ((1 + 7 * th2) / 15 - ε) - 4 * ((1 + 22 * th2) / 60 - 2 * ε) = -th2 + 7 * ε := by ring

/-- (5.16) lower end: `4β₄ + β₃ - 2 ≥ 2 - 4c₃ + c₁ - 2 ≥ -θ₂ + ε`. -/
theorem eq516_low {b3 b4 th2 ε : ℝ} (hε : 0 ≤ ε) (h4 : 1 / 2 - ((1 + 22 * th2) / 60 - 2 * ε) ≤ b4)
    (h3 : (1 + 7 * th2) / 15 - ε ≤ b3) : -th2 + ε ≤ 4 * b4 + b3 - 2 := by linarith

/-- (5.16) upper end, on `D` (`β₃ ≤ β₂ < β₁`, `β₁ + 2β₂ ≤ 1/2 + c₃`), for the paper's `θ₂`. -/
theorem eq516_high {b1 b2 b3 b4 ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 0.001) (h32 : b3 ≤ b2)
    (h21 : b2 < b1)
    (hD : b1 + 2 * b2 ≤ 1 / 2 + ((1 + 22 * (2 * (1 / 16 - 1 / 10 ^ 5))) / 60 - 2 * ε))
    (h4 : b4 ≤ 1 / 2 - (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 + 2 * ε) :
    4 * b4 + b3 - 2 < 2 * (1 / 16 - 1 / 10 ^ 5) - ε := by
  norm_num at hD h4 ⊢
  linarith

/-! ### `Q₂`, U-5153 -/

/-- `c₁ - (θ₂ - ε) = (1 - 8θ₂)/15`, positive for every `θ₂ < 1/8`. -/
theorem c1_gap (th2 ε : ℝ) : ((1 + 7 * th2) / 15 - ε) - (th2 - ε) = (1 - 8 * th2) / 15 := by ring

/-- The lower end of `P₂` on `Q₂` holds: `4(β₁ + β₂) + β₃ - 2 ≥ -θ₂ + 4ε`. -/
theorem Q2_low {b1 b2 b3 th2 c1 ε : ℝ} (hε : 0 ≤ ε) (hc1 : c1 ≤ b3)
    (hq2 : 1 / 2 - (th2 + c1) / 4 + ε ≤ b1 + b2) : -th2 + ε ≤ 4 * (b1 + b2) + b3 - 2 := by
  linarith

/-- FINDING F-5023, cosmetic, falsifier AGREE: the upper end of `P₂` fails on `Q₂` as printed, with `p₁p₂, p₃`
as in `Q₁`. For `δ > 0` small, `β₂ = β₃ = c₁ + δ`, `β₁ = 1/2 - c₁ - 5δ/4` lies in `Q₂`, with
`4β₁ + 5β₂ = 2 + c₁`, while `4(β₁ + β₂) + β₃ - 2 = c₁ > θ₂ - ε`; the point is in none of the
other cases of Lemma 33 for this grouping: `β₃ > c₁` rules out (5.13), `β₁ + β₂ > c₂` rules out
`R`, and `4(β₁ + β₂) + 3β₃ - 2 = 3c₁ + 2δ > θ₂` rules out `P₁`. Paper's `θ₂`, `0 < ε ≤ 0.001`. -/
theorem Q2_high_fails {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 0.001) (hδ : 0 < δ) (hδ1 : δ ≤ 0.001) :
    let th2 : ℝ := 2 * (1 / 16 - 1 / 10 ^ 5)
    let c1 : ℝ := (1 + 7 * th2) / 15 - ε
    let c2 : ℝ := (36 * th2 - 2) / 11 - ε
    let b2 : ℝ := c1 + δ
    let b3 : ℝ := c1 + δ
    let b1 : ℝ := 1 / 2 - c1 - 5 * δ / 4
    (c1 ≤ b2 ∧ b2 ≤ b1 ∧ b2 ≤ c2 ∧ 4 * b1 + 5 * b2 ≤ 2 + c1 ∧
        1 / 2 - (th2 + c1) / 4 + ε ≤ b1 + b2 ∧ c1 ≤ b3 ∧ b3 ≤ b2) ∧
      th2 - ε < 4 * (b1 + b2) + b3 - 2 ∧ c1 < b3 ∧ c2 < b1 + b2 ∧
      th2 - ε < 4 * (b1 + b2) + 3 * b3 - 2 := by
  intro th2 c1 c2 b2 b3 b1
  simp only [th2, c1, c2, b1, b2, b3]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> nlinarith

/-- Repair: with `4β₁ + 5β₂ ≤ 2 + θ₂ - ε` in place of `2 + c₁`, the upper end of `P₂` holds,
`4(β₁ + β₂) + β₃ - 2 ≤ θ₂ - ε`, so `Q₂` loses a strip of width `(1 - 8θ₂)/15 ≈ 1.1 × 10^-5`. -/
theorem Q2_repair {b1 b2 b3 th2 ε : ℝ} (h32 : b3 ≤ b2) (hq : 4 * b1 + 5 * b2 ≤ 2 + th2 - ε) :
    4 * (b1 + b2) + b3 - 2 ≤ th2 - ε := by linarith

end LeanLab.BHP1997.Lemma35
