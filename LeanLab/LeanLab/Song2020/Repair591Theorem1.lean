/-
AI wrote the Lean code. CODEX task591.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, page 2, Theorem 1, and page 9.
The sealed statement is moved unchanged and uses the existing assembly.
CONDITIONAL ON the open Fourier, logarithmic transfer and Lemma 3 inputs.
This theorem still has sorryAx. The exact window is not proved.
Binary Goldbach is open.
-/
import LeanLab.Song2020.DecompJ198

namespace LeanLab.Song2020

/-- P0078 Song 2020, Theorem 1. Cited, not proved here. -/
theorem song_theorem1 : SongTheorem1 := by
  exact DecompJ198.song_theorem1_decomposed

end LeanLab.Song2020

#print axioms LeanLab.Song2020.song_theorem1
