import LeanLab.ExceptionalSet.Decomp404e

/-!
P0082 pages 368 to370, the large value threshold used in the odd moment proof.
Lemma9 is printed with exponent minus one third on page368.
Its invocation on page369 uses exponent minus two thirds.
This file checks only the scalar implication between those thresholds.
It does not refute Lemma9, the odd moment estimate or Theorem1.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.ThresholdAudit467

/-- P0082 page368 Lemma9 and page369 after display38. A value can exceed
N E to minus two thirds without exceeding N E to minus one third. -/
theorem large_value_threshold_gap (E N : ℝ) (hE : 1 < E) (hN : 0 < N) :
    N * E ^ (-(2 / 3 : ℝ)) < N * E ^ (-(1 / 2 : ℝ)) ∧
      ¬ (N * E ^ (-(1 / 3 : ℝ)) < N * E ^ (-(1 / 2 : ℝ))) := by
  constructor
  · exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_exponent_lt hE (by norm_num)) hN
  · apply not_lt_of_ge
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)) hN.le

/-- P0082 page369 invocation of Lemma9. The larger value premise printed
in Lemma9 does not follow from the premise used at this step. A stronger
large value theorem or a revised choice of margins is still required. -/
theorem not_large_value_threshold_implication (E N : ℝ) (hE : 1 < E) (hN : 0 < N) :
    ¬ (∀ v : ℝ, N * E ^ (-(2 / 3 : ℝ)) < v →
      N * E ^ (-(1 / 3 : ℝ)) < v) := by
  intro h
  have hg := large_value_threshold_gap E N hE hN
  exact hg.2 (h _ hg.1)

/-- P0082 pages368 to370, a derived repair of the threshold invocation.
Halving the kappa supplied by the original Lemma9 matches the minus two thirds
threshold. Its height bound becomes E to four thirds. CONDITIONAL ON h9.
This theorem supplies no odd moment estimate. -/
theorem rescaled_lemma9 (h9 : LeanLab.ExceptionalSet.U1539.Lemma9)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
        |α| ≤ LeanLab.ExceptionalSet.BrudernPerelli1998.F γ N ^ δ →
        N * LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (-(2 / 3 : ℝ)) <
          ‖LeanLab.ExceptionalSet.U1539.Phie γ N α‖ →
        ∃ h : ℤ, (|h| : ℝ) ≤ LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (4 / 3 : ℝ) ∧
          |α - h / 2| ≤ LeanLab.ExceptionalSet.BrudernPerelli1998.F γ N ^ (δ - 1) := by
  obtain ⟨δ₀, hδ₀, hδ⟩ := h9 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδpos hδsmall => ?_⟩
  obtain ⟨κ, hκ, N₀, hb⟩ := hδ δ hδpos hδsmall
  refine ⟨κ / 2, by positivity, N₀, fun N hN α hα hlarge => ?_⟩
  have ht : LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (-(1 / 3 : ℝ)) =
      LeanLab.ExceptionalSet.U1539.calE γ (κ / 2) N ^ (-(2 / 3 : ℝ)) := by
    simp only [LeanLab.ExceptionalSet.U1539.calE, ← Real.exp_mul]
    congr 1
    ring
  have hh : LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (2 / 3 : ℝ) =
      LeanLab.ExceptionalSet.U1539.calE γ (κ / 2) N ^ (4 / 3 : ℝ) := by
    simp only [LeanLab.ExceptionalSet.U1539.calE, ← Real.exp_mul]
    congr 1
    ring
  obtain ⟨h, hheight, hgap⟩ := hb N hN α hα (by rwa [ht])
  exact ⟨h, by rwa [← hh], hgap⟩

/-- P0082 page369 after display38, derived uniform parameter repair.
For every positive height margin, the original Lemma9 localizes the values
above the minus two thirds threshold at every sufficiently small kappa.
The old height is absorbed into a power of X. CONDITIONAL ON h9. -/
theorem uniform_large_value_localization (h9 : LeanLab.ExceptionalSet.U1539.Lemma9)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
          |α| ≤ LeanLab.ExceptionalSet.BrudernPerelli1998.F γ N ^ δ →
          N * LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (-(2 / 3 : ℝ)) <
            ‖LeanLab.ExceptionalSet.U1539.Phie γ N α‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ LeanLab.ExceptionalSet.BrudernPerelli1998.F γ N ^ ε ∧
            |α - h / 2| ≤ LeanLab.ExceptionalSet.BrudernPerelli1998.F γ N ^ (δ - 1) := by
  obtain ⟨δ₀, hδ₀, hb⟩ := h9 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κold, hκold, Nold, hold⟩ := hb δ hδ hδsmall
  obtain ⟨Na, ha⟩ := LeanLab.ExceptionalSet.Decomp404e.calE_power_le_F_power
    γ κold (2 / 3) ε h1 hε
  refine ⟨κold / 2, by positivity, fun κ hκ hκsmall =>
    ⟨max 2 (max Nold Na), fun N hN α hα hlarge => ?_⟩⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNo : Nold ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNa : Na ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hscale : LeanLab.ExceptionalSet.U1539.calE γ κold N ^ (-(1 / 3 : ℝ)) ≤
      LeanLab.ExceptionalSet.U1539.calE γ κ N ^ (-(2 / 3 : ℝ)) := by
    simp only [LeanLab.ExceptionalSet.U1539.calE, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    nlinarith only [mul_nonneg (show 0 ≤ κold - 2 * κ by linarith) hp]
  have hlargeold : N * LeanLab.ExceptionalSet.U1539.calE γ κold N ^ (-(1 / 3 : ℝ)) <
      ‖LeanLab.ExceptionalSet.U1539.Phie γ N α‖ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg N)) hlarge
  obtain ⟨h, hh, hgap⟩ := hold N hNo α hα hlargeold
  exact ⟨h, hh.trans (ha N hNa), hgap⟩

end LeanLab.ExceptionalSet.ThresholdAudit467
