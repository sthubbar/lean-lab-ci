/-
P0089 Languasco 2004 survey: links between the quoted statements.
1. Page 225: if `E(X, 2) = ∅` for all large `X`, every large even number is a G-number.
2. A power saving `H^{1-η}` for `H ≥ X^a`, `a, η > 0`, implies a saving of every log power.
   So Theorem 1.8 gives Theorem 1.6's kind of bound on its own range, and Theorem 2.4 gives
   Theorem 2.3's kind of bound on its range.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Languasco2004.Statements

namespace LeanLab.Languasco2004
open Finset Real Asymptotics Filter

attribute [local instance] Classical.propDecidable

theorem mem_EXH {X H : ℝ} {n : ℕ} :
    n ∈ (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X ≤ (n : ℝ) ∧ (n : ℝ) ≤ X + H ∧ InE n) ↔
      X ≤ n ∧ (n : ℝ) ≤ X + H ∧ InE n := by
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (Nat.le_floor h.2.1), h⟩⟩

/-- **Page 225**: `E(X, 2) = ∅` for every `X ≥ X₀` makes every even `n > 2` with `n ≥ X₀` a
G-number. -/
theorem goldbach_of_E2_empty {X₀ : ℝ} (h : ∀ X : ℝ, X₀ ≤ X → EXH X 2 = 0) :
    ∀ n : ℕ, Even n → 2 < n → X₀ ≤ n → IsGoldbachSum n := by
  intro n he h2 hn
  by_contra hg
  have h0 := h n hn
  unfold EXH at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact h0 (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor (by linarith))))
    ⟨le_rfl, by linarith, he, h2, hg⟩

/-- **Power saving beats every log power**: if `|e(X,H)| ≤ C H^{1-η}` for `H ≥ X^a` with
`a, η > 0`, then for every `A > 0`, `|e(X,H)| ≤ H log^{-A} X` there for large `X`. -/
theorem logSaving_of_powerSaving (e : ℝ → ℝ → ℕ) {a η : ℝ} (ha : 0 < a) (hη : 0 < η)
    (h : PowerSaving e a η) : LogSaving e a := by
  intro A hA
  obtain ⟨C, X₀, hC⟩ := h
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- eventually `C' (log X)^A ≤ X^{aη}`
  have hlo := isLittleO_log_rpow_rpow_atTop A (mul_pos ha hη)
  have hev := hlo.bound (inv_pos.2 hC'pos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨X₁, hX₁⟩ := hev
  refine ⟨1, max (max X₀ X₁) 2, fun X H hX h1 => ?_⟩
  have hX0 : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) h1
  have hb := hX₁ X hX1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hXpos.le _)] at hb
  -- `C' L^A ≤ X^{aη}`
  have hb' : C' * Real.log X ^ A ≤ X ^ (a * η) := by
    have := mul_le_mul_of_nonneg_left hb hC'pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hC'pos.ne', one_mul] at this
  -- `H^{-η} ≤ X^{-aη}`
  have hHη : H ^ (-η) ≤ X ^ (-(a * η)) := by
    have : (X ^ a) ^ (-η) = X ^ (-(a * η)) := by
      rw [← Real.rpow_mul hXpos.le]; ring_nf
    rw [← this]
    exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXpos _) h1 (by linarith)
  have hLA : Real.log X ^ (-A) = (Real.log X ^ A)⁻¹ := Real.rpow_neg hL.le A
  have hXaη : X ^ (-(a * η)) = (X ^ (a * η))⁻¹ := Real.rpow_neg hXpos.le _
  have hLApos : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hXpos' : 0 < X ^ (a * η) := Real.rpow_pos_of_pos hXpos _
  -- `C' X^{-aη} ≤ L^{-A}`
  have hkey : C' * X ^ (-(a * η)) ≤ Real.log X ^ (-A) := by
    rw [hLA, hXaη, ← div_eq_mul_inv, div_le_iff₀ hXpos']
    calc C' = C' * Real.log X ^ A * (Real.log X ^ A)⁻¹ := by field_simp
      _ ≤ X ^ (a * η) * (Real.log X ^ A)⁻¹ := by gcongr
      _ = (Real.log X ^ A)⁻¹ * X ^ (a * η) := by ring
  have hsplit : H ^ (1 - η) = H * H ^ (-η) := by
    rw [sub_eq_add_neg, Real.rpow_add hHpos, Real.rpow_one]
  calc (e X H : ℝ) ≤ C * H ^ (1 - η) := hC X H hX0 h1
    _ ≤ C' * H ^ (1 - η) := by gcongr; exact le_max_left _ _
    _ = H * (C' * H ^ (-η)) := by rw [hsplit]; ring
    _ ≤ H * (C' * X ^ (-(a * η))) := by gcongr
    _ ≤ H * Real.log X ^ (-A) := by gcongr
    _ = 1 * H * Real.log X ^ (-A) := by ring

/-- Theorem 1.8 gives a saving of every log power on its own range `H ≥ X^{7/24+7δ}`, the kind of
bound of Theorems 1.5 and 1.6. -/
theorem thm18_logSaving (h : Thm18) : ∃ δ : ℝ, 0 < δ ∧ LogSaving EXH (7 / 24 + 7 * δ) := by
  obtain ⟨δ, hδ, hP⟩ := h
  exact ⟨δ, hδ, logSaving_of_powerSaving EXH (by positivity) (by positivity) hP⟩

/-- Theorem 2.4 gives Theorem 2.3's kind of bound on its range `H ≥ X^{7/12(1-1/k)+δ}`. -/
theorem thm24_logSaving (h : Thm24) (k : ℕ) (hk : 2 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ LogSaving (EkXH k) (7 / 12 * (1 - 1 / (k : ℝ)) + δ) := by
  obtain ⟨δ, hδ, hP⟩ := h k hk
  have hk' : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ k)
  have ha : 0 < 7 / 12 * (1 - 1 / (k : ℝ)) + δ := by nlinarith
  exact ⟨δ, hδ, logSaving_of_powerSaving (EkXH k) ha (by positivity) hP⟩

end LeanLab.Languasco2004
