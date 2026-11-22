/-
AI wrote the Lean code. CLAUDE S60 ROUTE BURST burst-20261122, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, Section 4, printed page 9.
Palomar entry for Song 2020 Theorem 1 with the fewest named inputs.

* Exact window, the sealed `SongTheorem1`: CONDITIONAL ON two named inputs,
  `Lemma3 (7 / 8)`, the paper's citation of Pan and Pan, Goldbach Conjecture, 1988,
  Theorem 3, and `Flag1734.LogTransferDQ`, the page 9 transfer at the exact threshold,
  QUESTION Q139c. Lemma 4 is not an input: the transfer statement already carries the
  discrepancy bound it needs.
* Window with any positive margin: CONDITIONAL ON one named input, `Lemma3 (7 / 8)`.
  Lemma 4 is discharged by `Wire1122Lemma4.song_lemma4_of_leaves`, Lemma 5 and the
  singular series bound are proved on main.

No existing file is changed and no sorry is added. Binary Goldbach is open.
-/
import LeanLab.Song2020.Wire1122Lemma4
import LeanLab.Song2020.Repair591Margin

namespace LeanLab.Song2020.Palomar1122Song

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- CONDITIONAL ON `Lemma3 (7 / 8)` and `Flag1734.LogTransferDQ`. Song 2020, page 9, the
display "By Lemma 3.3, Lemma 3.4 and Lemma 3.5, we have": the asymptotic formula for R(n),
assembled exactly as `Decomp139b.song_asymptotic_decomposed` with the cited Lemma 3 and the
exact window transfer taken as arguments. -/
theorem asymptotic_of_lemma3_logTransfer (H3 : Lemma3 (7 / 8))
    (HL : Flag1734.LogTransferDQ) : Asymptotic := by
  intro γ hγ hγ1
  obtain ⟨C₀, N₀, hmain⟩ := H3
  obtain ⟨C₁, N₁, hlog⟩ := HL γ hγ hγ1
  refine ⟨C₀ + C₁, max 1 (max N₀ N₁), ?_⟩
  intro n ho hn y hy hyupper
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsmall : (n : ℝ) ^ ((7 : ℝ) / 8) ≤ y :=
    (Real.rpow_le_rpow_of_exponent_le hnR (songExponent_mem hγ hγ1).1.le).trans hy.le
  have hmain' := hmain n ho (by omega) y hsmall hyupper
  obtain ⟨D, _, hD, hbudget⟩ := hlog n (by omega) y hy hyupper
  have herr := (Decomp139b.song_cube_transfer139 γ n y D hD).trans hbudget
  calc
    ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤
        ‖RS γ n y - gCube n y‖ + ‖gCube n y - (mainTerm n y : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C₁ * (y ^ 2 / Real.log (n : ℝ) ^ 4) + C₀ * (y ^ 2 / Real.log (n : ℝ) ^ 4) :=
      add_le_add herr hmain'
    _ = _ := by ring

/-- CONDITIONAL ON `Lemma3 (7 / 8)` and `Flag1734.LogTransferDQ`. Song 2020, Theorem 1, the
exact sealed window, by the page 9 deduction `songTheorem1_of_asymptotic139`. -/
theorem songTheorem1_of_lemma3_logTransfer (H3 : Lemma3 (7 / 8))
    (HL : Flag1734.LogTransferDQ) : SongTheorem1 :=
  songTheorem1_of_asymptotic139 (asymptotic_of_lemma3_logTransfer H3 HL)

/-- CONDITIONAL ON `Lemma3 (7 / 8)` only. Song 2020, Theorem 1 with any positive window margin
δ, page 9. Lemma 4 is the PROVED `Wire1122Lemma4.song_lemma4_of_leaves`. -/
theorem songWindow_margin_of_lemma3 (H3 : Lemma3 (7 / 8))
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ)
    (hθ : songExponent γ + δ < 1) : SongWindow γ (songExponent γ + δ) :=
  Repair591Margin.songWindow_with_margin591 H3 Wire1122Lemma4.song_lemma4_of_leaves
    γ hγ hγ1 δ hδ hθ

/-- CONDITIONAL ON `Lemma3 (7 / 8)` only. Song 2020, the page 9 asymptotic formula for R(n)
with any positive window margin δ. -/
theorem asymptotic_margin_of_lemma3 (H3 : Lemma3 (7 / 8))
    (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, Odd n → N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ (songExponent γ + δ) ≤ y → y ≤ (n : ℝ) / 3 →
      ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤ C * (y ^ 2 / Real.log (n : ℝ) ^ 4) :=
  Repair591Margin.asymptotic_with_margin591 H3 Wire1122Lemma4.song_lemma4_of_leaves
    γ hγ hγ1 δ hδ

end

end LeanLab.Song2020.Palomar1122Song

#print axioms LeanLab.Song2020.Palomar1122Song.asymptotic_of_lemma3_logTransfer
#print axioms LeanLab.Song2020.Palomar1122Song.songTheorem1_of_lemma3_logTransfer
#print axioms LeanLab.Song2020.Palomar1122Song.songWindow_margin_of_lemma3
#print axioms LeanLab.Song2020.Palomar1122Song.asymptotic_margin_of_lemma3
