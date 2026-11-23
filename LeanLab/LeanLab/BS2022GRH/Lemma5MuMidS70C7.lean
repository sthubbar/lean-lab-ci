/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 7 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 232825 ≤ N ≤ 295556: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 7 after the first two. -/
def cpts7 : List ℕ := [233885, 234416, 234942, 235470, 235993, 236518, 237045, 237577, 238109, 238642, 239172, 239704, 240234, 240766, 241304, 241841, 242385, 242921, 243460, 244005, 244554, 245101, 245653, 246202, 246754, 247308, 247857, 248402, 248950, 249504, 250056, 250612, 251165, 251713, 252262, 252808, 253357, 253906, 254457, 255009, 255564, 256125, 256685, 257240, 257801, 258358, 258913, 259468, 260021, 260573, 261137, 261700, 262265, 262830, 263392, 263953, 264522, 265088, 265658, 266221, 266788, 267354, 267921, 268492, 269060, 269625, 270198, 270765, 271333, 271913, 272493, 273066, 273641, 274222, 274800, 275380, 275960, 276536, 277112, 277693, 278273, 278848, 279428, 280004, 280580, 281157, 281730, 282304, 282880, 283450, 284018, 284582, 285152, 285720, 286288, 286860, 287437, 288006, 288578, 289145, 289720, 290298, 290873, 291448, 292028, 292612, 293198, 293788, 294378, 294970, 295556]

theorem chk7 : chkC P (232825 :: 233353 :: cpts7) = true := by decide +kernel

theorem last7 : lastOf 233353 cpts7 = 295556 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 232825 ≤ N ≤ 295556, by the kernel checked Legendre count. -/
theorem cover7 (N : ℕ) (h1 : 232825 ≤ N) (h2 : N ≤ 295556) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts7 232825 233353 chk7 N h1 (last7 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
