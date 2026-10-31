/-
P0071 Languasco and Perelli 1996, Theorem 4 and Corollary 2, pages 351 and 352, read from the
page images of papers/P0071.pdf. Unit U-5068, CLOUD 20261019T0213Z-cloud14.

STATED as cited: `GMCxi θ ξ`, the hypothesis GMC(θ; ξ), and `Theorem4 θ ξ`.
PROVED: `gmcxi_iff`, GMC(θ; ξ) with `ξ = 1/(qQ)`, `Q = X^θ/2`, is GMC(θ), since then
`W = Xξ/2 = X^{1-θ}/q = V`, as the paper observes; `cor2_of_thm4`, Corollary 2 from Theorem 4,
the paper's "we immediately get", with the step `X^{1/2+ε}(1 + (X/qQ)^{1/2}) ≤ 2X^{1+ε}/(qQ)^{1/2}`
since `qQ ≤ Q² ≤ X/4`; `eq6_exponent`, the bound of (6), `sup |S|² · ∫|S|²` with
`|S| ≪ X^{1+ε}/Q` and `∫|S|² ≪ X^{1+ε}` is `4 X^{3-2θ+3ε}`.
Every result assumes GRH and GMC(θ). Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib
import LeanLab.LanguascoPerelli1996.B.Statements

namespace LeanLab.LanguascoPerelli1996.B
open Real

noncomputable section

/-- GMC(θ; ξ), page 351: GRH and, for every `ε > 0`, `F(X, T; q, a) ≪_ε q² T X^ε` uniformly for
`W ≤ T ≤ X`, `q ≤ X^θ`, `(a, q) = 1`, where `W = Xξ/2` and `ξ = ξ(X, q)`. -/
def GMCxi (θ : ℝ) (ξ : ℝ → ℕ → ℝ) : Prop :=
  DERZ1997.GRH ∧ ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ (X T : ℝ) (q : ℕ) [NeZero q] (a : ℕ),
    X₀ ≤ X → X * ξ X q / 2 ≤ T → T ≤ X → (q : ℝ) ≤ X ^ θ → a.Coprime q →
      ‖F X T q a‖ ≤ C * (q : ℝ) ^ 2 * T * X ^ ε

/-- `ξ = 1/(qQ)` with `Q = X^θ/2`. -/
def xi0 (θ : ℝ) (X : ℝ) (q : ℕ) : ℝ := 1 / (q * (X ^ θ / 2))

/-- "GMC(θ; ξ) coincides with GMC(θ) if ξ = 1/qQ and Q = X^θ/2", page 351, for `X > 0`. -/
theorem W_eq {θ X : ℝ} (hX : 0 < X) (q : ℕ) (hq : 0 < q) :
    X * xi0 θ X q / 2 = X ^ (1 - θ) / q := by
  unfold xi0
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hXθ : 0 < X ^ θ := rpow_pos_of_pos hX θ
  rw [rpow_sub hX, rpow_one]
  field_simp

theorem gmcxi_iff (θ : ℝ) : GMCxi θ (xi0 θ) ↔ GMC θ := by
  unfold GMCxi GMC
  refine and_congr_right fun _ => forall₂_congr fun ε _ => ?_
  constructor
  · rintro ⟨C, X₀, h⟩
    refine ⟨C, max X₀ 1, fun X T q _ a hX hT hTX hq ha => ?_⟩
    have hX0 : 0 < X := by linarith [le_max_right X₀ 1]
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact h X T q a (le_trans (le_max_left _ _) hX) (by rw [W_eq hX0 q hqpos]; exact hT) hTX hq ha
  · rintro ⟨C, X₀, h⟩
    refine ⟨C, max X₀ 1, fun X T q _ a hX hT hTX hq ha => ?_⟩
    have hX0 : 0 < X := by linarith [le_max_right X₀ 1]
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact h X T q a (le_trans (le_max_left _ _) hX) (by rw [← W_eq hX0 q hqpos]; exact hT) hTX hq ha

/-- Theorem 4, page 351, CITED: for `θ ∈ (0, 1/2]`, `ξ(X, q) ∈ (0, 1/2]` and GMC(θ; ξ), for every
`ε > 0`, `S(a/q + η) = μ(q)/φ(q) T(η) + O_ε(X^{1/2+ε}(1 + (Xξ)^{1/2}))` uniformly for `q ≤ X^θ`,
`(a, q) = 1` and `|η| ≤ ξ`. The range of `ξ` is asked for large `X`. -/
def Theorem4 (θ : ℝ) (ξ : ℝ → ℕ → ℝ) : Prop :=
  (∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → ∀ q : ℕ, 1 ≤ q → 0 < ξ X q ∧ ξ X q ≤ 1 / 2) →
  GMCxi θ ξ → ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ (X η : ℝ) (q a : ℕ), X₀ ≤ X → 1 ≤ q →
    (q : ℝ) ≤ X ^ θ → a.Coprime q → |η| ≤ ξ X q →
      ‖R X η q a‖ ≤ C * X ^ (1 / 2 + ε) * (1 + (X * ξ X q) ^ (1 / 2 : ℝ))

/-- Corollary 2, page 352: for `θ ∈ (0, 1/2]`, `Q = X^θ/2` and GMC(θ), for every `ε > 0`,
`S(a/q + η) = μ(q)/φ(q) T(η) + O_ε(X^{1+ε}/(qQ)^{1/2})` uniformly for `q ≤ Q`, `(a, q) = 1`,
`|η| ≤ 1/qQ`. -/
def Cor2 (θ : ℝ) : Prop :=
  GMC θ → ∀ ε : ℝ, 0 < ε → ∃ C X₀ : ℝ, ∀ (X η : ℝ) (q a : ℕ), X₀ ≤ X → 1 ≤ q →
    (q : ℝ) ≤ X ^ θ / 2 → a.Coprime q → |η| ≤ 1 / (q * (X ^ θ / 2)) →
      ‖R X η q a‖ ≤ C * X ^ (1 + ε) / ((q : ℝ) * (X ^ θ / 2)) ^ (1 / 2 : ℝ)

/-- The range condition for `ξ = 1/(qQ)`: `0 < ξ ≤ 1/2` once `X^θ ≥ 4`. -/
theorem xi0_range {θ : ℝ} (hθ : 0 < θ) :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → ∀ q : ℕ, 1 ≤ q → 0 < xi0 θ X q ∧ xi0 θ X q ≤ 1 / 2 := by
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hθ).eventually (Filter.eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ 1, fun X hX q hq => ?_⟩
  have h4 : 4 ≤ X ^ θ := hX₁ X (le_trans (le_max_left _ _) hX)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold xi0
  have hpos : 0 < (q : ℝ) * (X ^ θ / 2) := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith

/-- The step of Corollary 2: for `1 ≤ y`, `X^{1/2+ε}(1 + y^{1/2}) ≤ 2 X^{1/2+ε} y^{1/2}`, and with
`y = X/(qQ)` the right side is `2 X^{1+ε}/(qQ)^{1/2}`. -/
theorem step {X ε D : ℝ} (hX : 0 < X) (hD : 0 < D) (hy : 1 ≤ X / D) :
    X ^ (1 / 2 + ε) * (1 + (X / D) ^ (1 / 2 : ℝ)) ≤ 2 * (X ^ (1 + ε) / D ^ (1 / 2 : ℝ)) := by
  have h1 : 1 ≤ (X / D) ^ (1 / 2 : ℝ) := one_le_rpow hy (by norm_num)
  have hXe : 0 < X ^ (1 / 2 + ε) := rpow_pos_of_pos hX _
  have key : X ^ (1 / 2 + ε) * (X / D) ^ (1 / 2 : ℝ) = X ^ (1 + ε) / D ^ (1 / 2 : ℝ) := by
    rw [div_rpow hX.le hD.le, mul_div_assoc', ← rpow_add hX]
    congr 2; ring
  have : X ^ (1 / 2 + ε) * (1 + (X / D) ^ (1 / 2 : ℝ)) ≤
      2 * (X ^ (1 / 2 + ε) * (X / D) ^ (1 / 2 : ℝ)) := by nlinarith
  rw [key] at this; exact this

/-- `qQ ≤ Q² ≤ X/4` for `q ≤ Q = X^θ/2`, `θ ≤ 1/2`, `X ≥ 1`. -/
theorem qQ_le {θ X : ℝ} (hθ : θ ≤ 1 / 2) (hX : 1 ≤ X) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ X ^ θ / 2) : q * (X ^ θ / 2) ≤ X / 4 := by
  have hXθ : X ^ θ ≤ X ^ (1 / 2 : ℝ) := rpow_le_rpow_of_exponent_le hX hθ
  have hsq : (X ^ (1 / 2 : ℝ)) ^ 2 = X := by
    rw [← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have h0 : 0 ≤ X ^ θ := rpow_nonneg (by linarith) _
  have : q * (X ^ θ / 2) ≤ (X ^ θ / 2) * (X ^ θ / 2) := mul_le_mul_of_nonneg_right hq (by positivity)
  nlinarith [mul_le_mul hXθ hXθ h0 (rpow_nonneg (by linarith) _)]

/-- Corollary 2 from Theorem 4, the paper's "we immediately get". -/
theorem cor2_of_thm4 {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) (h4 : Theorem4 θ (xi0 θ)) :
    Cor2 θ := by
  intro hG ε hε
  obtain ⟨C, X₀, hC⟩ := h4 (xi0_range hθ) ((gmcxi_iff θ).mpr hG) ε hε
  refine ⟨2 * |C|, max X₀ 1, fun X η q a hX hq hqQ ha hη => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hXθ : 0 < X ^ θ := rpow_pos_of_pos hX0 θ
  have hqθ : (q : ℝ) ≤ X ^ θ := by linarith
  set D := (q : ℝ) * (X ^ θ / 2) with hDdef
  have hD : 0 < D := by positivity
  have hDle : D ≤ X / 4 := qQ_le hθ1 hX1 (by linarith) hqQ
  have hy : 1 ≤ X / D := by rw [le_div_iff₀ hD]; linarith
  have hb := hC X η q a (le_trans (le_max_left _ _) hX) hq hqθ ha (by unfold xi0; exact hη)
  have hxi : X * xi0 θ X q = X / D := by unfold xi0; rw [hDdef]; field_simp
  rw [hxi] at hb
  have hs := step (ε := ε) hX0 hD hy
  have hpos : 0 ≤ X ^ (1 / 2 + ε) * (1 + (X / D) ^ (1 / 2 : ℝ)) := by positivity
  calc ‖R X η q a‖ ≤ C * X ^ (1 / 2 + ε) * (1 + (X / D) ^ (1 / 2 : ℝ)) := hb
    _ ≤ |C| * (X ^ (1 / 2 + ε) * (1 + (X / D) ^ (1 / 2 : ℝ))) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hpos
    _ ≤ |C| * (2 * (X ^ (1 + ε) / D ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hs (abs_nonneg C)
    _ = 2 * |C| * X ^ (1 + ε) / D ^ (1 / 2 : ℝ) := by ring

/-- (6), in exponents: `sup_m |S|² ∫|S|²` with `|S| ≪ X^{1+ε}/Q`, `Q = X^θ/2`, and
`∫₀¹ |S|² ≪ X^{1+ε}` is `4 X^{3-2θ+3ε}`; the exceptional set bound then reads `E(X) X² ≪ X^{3-2θ+ε}`,
`E(X) ≪ X^{1-2θ+ε}`. -/
theorem eq6_exponent {X θ ε : ℝ} (hX : 0 < X) :
    (X ^ (1 + ε) / (X ^ θ / 2)) ^ 2 * X ^ (1 + ε) = 4 * X ^ (3 - 2 * θ + 3 * ε) := by
  have hXθ : 0 < X ^ θ := rpow_pos_of_pos hX θ
  have e1 : X ^ (3 - 2 * θ + 3 * ε) * (X ^ θ) ^ 2 = (X ^ (1 + ε)) ^ 2 * X ^ (1 + ε) := by
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul hX.le, ← rpow_mul hX.le, ← rpow_add hX,
      ← rpow_add hX]
    congr 1; push_cast; ring
  field_simp
  ring_nf at e1 ⊢
  linear_combination (-4) * e1

end

end LeanLab.LanguascoPerelli1996.B

