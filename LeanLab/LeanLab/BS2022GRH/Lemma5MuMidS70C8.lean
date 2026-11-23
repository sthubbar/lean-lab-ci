/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 8 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 295556 ≤ N ≤ 363858: kernel check of the Legendre count at 113 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 8 after the first two. -/
def cpts8 : List ℕ := [296722, 297308, 297898, 298490, 299084, 299678, 300272, 300864, 301462, 302062, 302658, 303252, 303844, 304434, 305022, 305613, 306205, 306794, 307381, 307973, 308560, 309152, 309746, 310340, 310937, 311533, 312130, 312728, 313320, 313914, 314516, 315110, 315704, 316302, 316902, 317500, 318096, 318693, 319290, 319890, 320493, 321094, 321698, 322305, 322912, 323517, 324122, 324732, 325342, 325945, 326552, 327157, 327772, 328384, 329000, 329617, 330230, 330842, 331462, 332085, 332708, 333329, 333954, 334576, 335198, 335820, 336434, 337048, 337665, 338278, 338890, 339502, 340110, 340725, 341337, 341950, 342568, 343182, 343796, 344410, 345026, 345640, 346262, 346885, 347506, 348122, 348744, 349366, 349981, 350597, 351213, 351837, 352460, 353089, 353718, 354341, 354976, 355608, 356234, 356865, 357496, 358128, 358762, 359397, 360032, 360666, 361302, 361942, 362585, 363222, 363858]

theorem chk8 : chkC P (295556 :: 296141 :: cpts8) = true := by decide +kernel

theorem last8 : lastOf 296141 cpts8 = 363858 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 295556 ≤ N ≤ 363858, by the kernel checked Legendre count. -/
theorem cover8 (N : ℕ) (h1 : 295556 ≤ N) (h2 : N ≤ 363858) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts8 295556 296141 chk8 N h1 (last8 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
