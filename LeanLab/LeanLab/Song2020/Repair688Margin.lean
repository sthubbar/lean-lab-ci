/-
AI wrote the Lean code. CODEX task688, 2026-11-24.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, printed page 9.
This is the derived transfer with an explicit positive window margin.
The sealed Flag1734.logTransferMargin statement moves here unchanged.
Its proof now uses the closed Lemma 4 route and the proved Lemma 5.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Wire1122Lemma4

namespace LeanLab.Song2020.Flag1734

/-- The corrected statement with the lab's proved Lemma 4 and Lemma 5. -/
theorem logTransferMargin (δ : ℝ) (hδ : 0 < δ) : LogTransferMarginDQ δ :=
  logTransferMargin_of LeanLab.Song2020.Wire1122Lemma4.song_lemma4_of_leaves
    LeanLab.Song2020.State1562.song_lemma5 δ hδ

end LeanLab.Song2020.Flag1734

#print axioms LeanLab.Song2020.Flag1734.logTransferMargin
