/-
P0071 Languasco-Perelli 1996, page 351: Corollary 1 from Theorems 2 and 3, and its second
assertion from its first by subdividing `[X, 2X]` into `≪ X^{1-2θ}` intervals `[Yⱼ, Yⱼ + Yⱼ^{2θ}]`,
as the paper sketches. Both are implications; the cited theorems stay cited.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LanguascoPerelli1996.B.Statements

namespace LeanLab.LanguascoPerelli1996.B
open Finset Real

attribute [local instance] Classical.propDecidable

theorem mem_Eset {X H : ℝ} {n : ℕ} :
    n ∈ Eset X H ↔ X ≤ n ∧ (n : ℝ) ≤ X + H ∧ Even n ∧ ¬ IsGoldbachSum n := by
  unfold Eset
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.1), h⟩

/-- `E(X, H)` grows with `H`. -/
theorem E_mono {X H H' : ℝ} (h : H ≤ H') : E X H ≤ E X H' := by
  apply Finset.card_le_card
  intro n hn
  rw [mem_Eset] at hn ⊢
  exact ⟨hn.1, by linarith [hn.2.1], hn.2.2⟩

/-- **Corollary 1, first assertion, from Theorems 2 and 3**: for `θ ∈ (0, 1/2]`, GMC(θ) gives
`E(X, X^{2θ}) ≪_ε X^ε`. Theorem 3 supplies (5) with `Q = X^θ/2`; that `Q` lies in Theorem 2's
range `X^{ε'} ≤ Q ≤ X^{1/2}/2` for `ε' = min(ε, θ/2)` and `X` large; and `4Q² = X^{2θ}`. -/
theorem cor1a_of (h2 : Theorem2) {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) (h3 : Theorem3 θ)
    (hG : GMC θ) : Cor1a θ := by
  intro ε hε
  set ε' := min ε (θ / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by linarith)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'θ : ε' ≤ θ / 2 := min_le_right _ _
  obtain ⟨C, X₀, hC⟩ := h3 hG ε' hε'0
  obtain ⟨C', X₁, hC'⟩ := h2 hG.1 ε' hε'0 C
  set X₂ : ℝ := (2 : ℝ) ^ (1 / (θ - ε')) with hX₂
  refine ⟨max C' 0, max (max X₀ X₁) (max X₂ 1), fun X hX => ?_⟩
  have hX0 : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXone : 1 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have hd : 0 < θ - ε' := by linarith
  -- `X^{θ-ε'} ≥ 2`
  have hpow2 : 2 ≤ X ^ (θ - ε') := by
    have hX₂pos : 0 ≤ X₂ := by positivity
    calc (2 : ℝ) = X₂ ^ (θ - ε') := by
          rw [hX₂, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hd.ne', Real.rpow_one]
      _ ≤ X ^ (θ - ε') := Real.rpow_le_rpow hX₂pos hX2 hd.le
  -- `X^{ε'} ≤ X^θ / 2`
  have hlow : X ^ ε' ≤ X ^ θ / 2 := by
    have : X ^ θ = X ^ ε' * X ^ (θ - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    have hp : 0 < X ^ ε' := Real.rpow_pos_of_pos hXpos _
    rw [this]; nlinarith
  -- `X^θ / 2 ≤ X^{1/2} / 2`
  have hup : X ^ θ / 2 ≤ X ^ ((1 : ℝ) / 2) / 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hXone h1
    linarith
  have hE := hC' X (X ^ θ / 2) hX1 hlow hup (hC X hX0)
  -- `4 (X^θ/2)² = X^{2θ}`
  have hsq : 4 * (X ^ θ / 2) ^ 2 = X ^ (2 * θ) := by
    have : (X ^ θ) ^ 2 = X ^ (2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; ring_nf
    rw [← this]; ring
  rw [hsq] at hE
  calc (E X (X ^ (2 * θ)) : ℝ) ≤ C' * X ^ ε' := hE
    _ ≤ max C' 0 * X ^ ε' := by
        gcongr; exact le_max_left _ _
    _ ≤ max C' 0 * X ^ ε := by
        gcongr

/-- **Corollary 1, second assertion, from the first**: subdivide `[X, 2X]` into the
`N + 1 ≤ 2 X^{1-2θ}` intervals `[Yⱼ, Yⱼ + h]`, `h = X^{2θ}`, `Yⱼ = X + j h`, `N = ⌊X / h⌋`;
each lies in `[Yⱼ, Yⱼ + Yⱼ^{2θ}]` and `Yⱼ ≤ 2X`. Needs only `0 ≤ θ ≤ 1/2`. -/
theorem cor1b_of_cor1a {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) (h : Cor1a θ) : Cor1b θ := by
  intro ε hε
  obtain ⟨C, X₀, hC⟩ := h ε hε
  refine ⟨2 * 2 ^ ε * max C 0, max X₀ 1, fun X hX => ?_⟩
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXone : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  set h := X ^ (2 * θ) with hh
  have hhpos : 0 < h := Real.rpow_pos_of_pos hXpos _
  set N := ⌊X / h⌋₊ with hN
  let Y : ℕ → ℝ := fun j => X + j * h
  -- every exceptional `n` in `[X, 2X]` lies in some `Eset (Y j) (Y j ^ (2θ))`
  have hsub : Eset X X ⊆ (Finset.range (N + 1)).biUnion (fun j => Eset (Y j) (Y j ^ (2 * θ))) := by
    intro n hn
    rw [mem_Eset] at hn
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
    set j := ⌊((n : ℝ) - X) / h⌋₊ with hj
    have hq0 : 0 ≤ ((n : ℝ) - X) / h := div_nonneg (by linarith) hhpos.le
    have hjN : j ≤ N := Nat.floor_le_floor (by
      apply div_le_div_of_nonneg_right _ hhpos.le; linarith)
    have hjle : (j : ℝ) ≤ ((n : ℝ) - X) / h := Nat.floor_le hq0
    have hjlt : ((n : ℝ) - X) / h < j + 1 := Nat.lt_floor_add_one _
    have hYle : Y j ≤ n := by
      have := (le_div_iff₀ hhpos).1 hjle
      simp only [Y]; linarith
    have hnlt : (n : ℝ) < Y j + h := by
      have := (div_lt_iff₀ hhpos).1 hjlt
      simp only [Y]; linarith
    have hXY : X ≤ Y j := by
      simp only [Y]; have : (0 : ℝ) ≤ j * h := by positivity
      linarith
    have hhY : h ≤ Y j ^ (2 * θ) := Real.rpow_le_rpow hXpos.le hXY (by linarith)
    rw [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hjN), ?_⟩
    rw [mem_Eset]
    exact ⟨hYle, by linarith, hn3, hn4⟩
  -- each piece is at most `C (2X)^ε`
  have hpiece : ∀ j ∈ Finset.range (N + 1),
      ((Eset (Y j) (Y j ^ (2 * θ))).card : ℝ) ≤ max C 0 * (2 ^ ε * X ^ ε) := by
    intro j hj
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hNle : (N : ℝ) ≤ X / h := Nat.floor_le (div_nonneg hXpos.le hhpos.le)
    have hXY : X ≤ Y j := by
      simp only [Y]; have : (0 : ℝ) ≤ j * h := by positivity
      linarith
    have hY2 : Y j ≤ 2 * X := by
      simp only [Y]
      have : (j : ℝ) * h ≤ X := by
        calc (j : ℝ) * h ≤ (X / h) * h := by gcongr; linarith
          _ = X := div_mul_cancel₀ X hhpos.ne'
      linarith
    have hYpos : 0 < Y j := by linarith
    calc ((Eset (Y j) (Y j ^ (2 * θ))).card : ℝ) ≤ C * Y j ^ ε := hC (Y j) (by linarith)
      _ ≤ max C 0 * Y j ^ ε := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (2 * X) ^ ε := by
          gcongr
      _ = max C 0 * (2 ^ ε * X ^ ε) := by
          rw [Real.mul_rpow (by norm_num) hXpos.le]
  -- `N + 1 ≤ 2 X^{1-2θ}`
  have hcount : ((N : ℝ) + 1) ≤ 2 * X ^ (1 - 2 * θ) := by
    have hNle : (N : ℝ) ≤ X / h := Nat.floor_le (div_nonneg hXpos.le hhpos.le)
    have hdiv : X / h = X ^ (1 - 2 * θ) := by
      rw [hh, Real.rpow_sub hXpos, Real.rpow_one]
    have hone : 1 ≤ X ^ (1 - 2 * θ) := Real.one_le_rpow hXone (by linarith)
    linarith
  have hEle : (E X X : ℝ) ≤ ∑ j ∈ Finset.range (N + 1),
      ((Eset (Y j) (Y j ^ (2 * θ))).card : ℝ) := by
    unfold E
    have := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    exact_mod_cast this
  have hK : 0 ≤ max C 0 * (2 ^ ε * X ^ ε) := by positivity
  calc (E X X : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), ((Eset (Y j) (Y j ^ (2 * θ))).card : ℝ) := hEle
    _ ≤ ∑ _j ∈ Finset.range (N + 1), max C 0 * (2 ^ ε * X ^ ε) := Finset.sum_le_sum hpiece
    _ = ((N : ℝ) + 1) * (max C 0 * (2 ^ ε * X ^ ε)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (2 * X ^ (1 - 2 * θ)) * (max C 0 * (2 ^ ε * X ^ ε)) := by gcongr
    _ = 2 * 2 ^ ε * max C 0 * X ^ (1 - 2 * θ + ε) := by
        rw [Real.rpow_add hXpos]; ring

/-- **Corollary 1, both assertions, from Theorems 2 and 3**, zero sorry as an implication. -/
theorem cor1_of (h2 : Theorem2) {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1 / 2) (h3 : Theorem3 θ)
    (hG : GMC θ) : Cor1a θ ∧ Cor1b θ :=
  ⟨cor1a_of h2 h0 h1 h3 hG, cor1b_of_cor1a h0.le h1 (cor1a_of h2 h0 h1 h3 hG)⟩

/-- GMC(θ) with `θ > 1/4` beats the GRH bound `E(X) ≪ X^{1/2+ε}` of Hardy-Littlewood quoted on
page 351: the exponent `1 - 2θ + ε` is below `1/2 + ε` exactly when `θ > 1/4`. -/
theorem exponent_lt_iff (θ ε : ℝ) : 1 - 2 * θ + ε < 1 / 2 + ε ↔ 1 / 4 < θ := by
  constructor <;> intro h <;> linarith

end LeanLab.LanguascoPerelli1996.B

