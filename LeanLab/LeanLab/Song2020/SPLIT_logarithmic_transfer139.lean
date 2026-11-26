/-
AI wrote the Lean code. CLOUD S1 ROUTE BURST burst-20261124.
Source: Song 2020, https://arxiv.org/pdf/2012.06322, Section 4, printed page 9,
the Cauchy step that feeds Lemma 4 and Lemma 5 into the cubic perturbation bound.
SPLIT of `Decomp139b.logarithmic_transfer139`.

The away range, y at least n to the songExponent plus delta, is already PROVED from Lemma 4
in `Repair591Margin.logarithmic_transfer_with_margin591`. The printed deduction fails only
near the endpoint of the window, as `Audit1122Absorption.printed_absorption_false` shows.
This file isolates exactly that endpoint content as one LEAF: the page 4 Lemma 4 discrepancy
at the endpoint of the window, with the n to the epsilon loss replaced by a saving of the
fourth power of log n. With Lemma 5, which is PROVED as `State1562.song_lemma5`, that LEAF
and the margin theorem give the exact statement of `logarithmic_transfer139`.

The existing file Decomp139b.lean is unchanged; it cannot import this file, since this file
imports Repair591Margin, which imports Decomp139b.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Repair591Margin

namespace LeanLab.Song2020.SplitLogTransfer139

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- LEAF: page 4 Lemma 4 at the window endpoint, as used on page 9. HARD.
For y between n^songExponent and n^(songExponent + δ), f - g is at most
C y n^(γ-1) / log^4 n, uniformly in α. At y = n^songExponent the printed Lemma 4 bound is
y n^(γ-1) n^ε, so this is Lemma 4 there with n^ε replaced by a log saving, the estimate the
page 9 step needs, QUESTION Q139c. Heuristic size at α = 0 in the notes; no refutation known. -/
theorem endpoint_discrepancy139 :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y < (n : ℝ) ^ (songExponent γ + δ) →
        y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ‖fS γ n y α - gS n y α‖ ≤
            C * (y * (n : ℝ) ^ (γ - 1) / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- PROVED from the LEAF and Lemma 5. Page 9 Cauchy step on the endpoint range: the endpoint
discrepancy times the two Lemma 5 mean squares is O of y squared over log to the fourth n. -/
theorem endpoint_transfer139 (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ C : ℝ) (N₀ : ℕ)
    (hL : ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y < (n : ℝ) ^ (songExponent γ + δ) →
        y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ‖fS γ n y α - gS n y α‖ ≤
            C * (y * (n : ℝ) ^ (γ - 1) / Real.log (n : ℝ) ^ 4)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y < (n : ℝ) ^ (songExponent γ + δ) →
      y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C' * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨C₅, N₅, h₅⟩ := song_lemma5 γ hγ hγ1
  refine ⟨4 * |C| * |C₅|, by positivity, max 1 (max N₀ N₅), ?_⟩
  intro n hn y hy hyδ hy3
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans hy
  set L := Real.log (n : ℝ) ^ 4 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact pow_nonneg (Real.log_nonneg hn1) 4
  set E := (n : ℝ) ^ (γ - 1) with hEdef
  set F := (n : ℝ) ^ (1 - γ) with hFdef
  have hE0 : 0 ≤ E := Real.rpow_nonneg hn0.le _
  have hF0 : 0 ≤ F := Real.rpow_nonneg hn0.le _
  have hEF : E * F = 1 := by
    rw [hEdef, hFdef, ← Real.rpow_add hn0, show γ - 1 + (1 - γ) = 0 by ring, Real.rpow_zero]
  have hE1 : E ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  obtain ⟨hf, hg⟩ := h₅ n (by omega) y hy hy3
  have hf' : (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) ≤ |C₅| * (F * y) :=
    hf.trans (mul_le_mul_of_nonneg_right (le_abs_self C₅) (by positivity))
  have hg' : (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ |C₅| * y :=
    hg.trans (mul_le_mul_of_nonneg_right (le_abs_self C₅) hy0.le)
  have hB0 : 0 ≤ y * E / L := by positivity
  refine ⟨|C| * (y * E / L), by positivity, ?_, ?_⟩
  · intro α
    exact (hL n (by omega) y hy hyδ hy3 α).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)
  · have hsum : E * (F * y + y) ≤ 2 * y := by
      have : E * (F * y + y) = (E * F) * y + E * y := by ring
      rw [this, hEF]
      nlinarith
    calc
      _ ≤ 2 * (|C| * (y * E / L)) * (|C₅| * (F * y) + |C₅| * y) :=
        mul_le_mul_of_nonneg_left (add_le_add hf' hg') (by positivity)
      _ = 2 * |C| * |C₅| * (y / L) * (E * (F * y + y)) := by ring
      _ ≤ 2 * |C| * |C₅| * (y / L) * (2 * y) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring

/-- CONDITIONAL ON `endpoint_discrepancy139` and Lemma 4. The exact statement of
`Decomp139b.logarithmic_transfer139`, page 9: the endpoint range from the LEAF and Lemma 5,
the away range from `Repair591Margin.logarithmic_transfer_with_margin591`. -/
theorem logarithmic_transfer139_split (H4 : Lemma4) :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
          2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
              C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  intro γ hγ hγ1
  obtain ⟨δ, hδ, CL, NL, hL⟩ := endpoint_discrepancy139 γ hγ hγ1
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := endpoint_transfer139 γ hγ hγ1 δ CL NL hL
  obtain ⟨C₂, hC₂, N₂, h₂⟩ :=
    Repair591Margin.logarithmic_transfer_with_margin591 H4 γ hγ hγ1 δ hδ
  refine ⟨max C₁ C₂, max 1 (max N₁ N₂), ?_⟩
  intro n hn y hy hy3
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hR : 0 ≤ y ^ 2 / Real.log (n : ℝ) ^ 4 :=
    div_nonneg (sq_nonneg y) (pow_nonneg (Real.log_nonneg hn1) 4)
  by_cases hyδ : y < (n : ℝ) ^ (songExponent γ + δ)
  · obtain ⟨D, hD0, hD, hb⟩ := h₁ n (by omega) y hy hyδ hy3
    exact ⟨D, hD0, hD, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hR)⟩
  · obtain ⟨D, hD0, hD, hb⟩ := h₂ n (by omega) y (not_lt.mp hyδ) hy3
    exact ⟨D, hD0, hD, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)⟩

end

end LeanLab.Song2020.SplitLogTransfer139

#print axioms LeanLab.Song2020.SplitLogTransfer139.endpoint_discrepancy139
#print axioms LeanLab.Song2020.SplitLogTransfer139.endpoint_transfer139
#print axioms LeanLab.Song2020.SplitLogTransfer139.logarithmic_transfer139_split
