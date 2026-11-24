/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit buthe_compute_mid.
Chunk 9 of the short computer calculation behind Buthe 2014 display 4.6, upper half,
for 363858 ≤ N ≤ 438652: kernel check of the Legendre count at 109 checkpoints.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.Lemma5MuMidS70

namespace LeanLab.BS2022GRH.Lemma5MuMidS70

/-- Checkpoints of chunk 9 after the first two. -/
def cpts9 : List ℕ := [365146, 365798, 366445, 367090, 367740, 368397, 369058, 369712, 370364, 371021, 371677, 372334, 372993, 373650, 374313, 374973, 375644, 376313, 376978, 377650, 378321, 378992, 379668, 380340, 381016, 381693, 382366, 383040, 383716, 384390, 385060, 385728, 386402, 387082, 387762, 388445, 389126, 389804, 390486, 391168, 391848, 392536, 393220, 393905, 394592, 395289, 395984, 396680, 397372, 398064, 398764, 399462, 400160, 400861, 401565, 402270, 402977, 403681, 404389, 405101, 405813, 406522, 407230, 407941, 408652, 409360, 410065, 410769, 411477, 412185, 412885, 413598, 414310, 415018, 415726, 416434, 417144, 417852, 418573, 419290, 420017, 420744, 421468, 422201, 422928, 423657, 424380, 425106, 425837, 426566, 427298, 428026, 428766, 429502, 430234, 430970, 431709, 432441, 433176, 433909, 434644, 435384, 436128, 436876, 437625, 438370, 438652]

theorem chk9 : chkC P (363858 :: 364500 :: cpts9) = true := by decide +kernel

theorem last9 : lastOf 364500 cpts9 = 438652 := by decide +kernel

/-- PROVED: Buthe 2014 display 4.6 upper half in integer form, `Q(N) ≤ 0.6079 N + 0.68 √N`,
for 363858 ≤ N ≤ 438652, by the kernel checked Legendre count. -/
theorem cover9 (N : ℕ) (h1 : 363858 ≤ N) (h2 : N ≤ 438652) :
    (S N : ℝ) ≤ 0.6079 * N + 0.68 * √(N : ℝ) :=
  chkC_sound P P_two_le P_sorted P_coprime cpts9 363858 364500 chk9 N h1 (last9 ▸ h2)

end LeanLab.BS2022GRH.Lemma5MuMidS70
