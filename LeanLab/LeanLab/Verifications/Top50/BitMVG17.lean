/-
Kernel Goldbach windows MV161 to MV170, width 990000, even n in [482140002, 492040000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV161: every even n in [482140002, 483130000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v161 : wem 482138190 482140002 483130000 &&& gm (wpm2 482138190 991810) (P10k.take 278) =
    wem 482138190 482140002 483130000 := by
  decide +kernel

/-- Window MV162: every even n in [483130002, 484120000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v162 : wem 483128190 483130002 484120000 &&& gm (wpm2 483128190 991810) (P10k.take 278) =
    wem 483128190 483130002 484120000 := by
  decide +kernel

/-- Window MV163: every even n in [484120002, 485110000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v163 : wem 484118190 484120002 485110000 &&& gm (wpm2 484118190 991810) (P10k.take 278) =
    wem 484118190 484120002 485110000 := by
  decide +kernel

/-- Window MV164: every even n in [485110002, 486100000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v164 : wem 485108190 485110002 486100000 &&& gm (wpm2 485108190 991810) (P10k.take 278) =
    wem 485108190 485110002 486100000 := by
  decide +kernel

/-- Window MV165: every even n in [486100002, 487090000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v165 : wem 486098190 486100002 487090000 &&& gm (wpm2 486098190 991810) (P10k.take 278) =
    wem 486098190 486100002 487090000 := by
  decide +kernel

/-- Window MV166: every even n in [487090002, 488080000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v166 : wem 487088190 487090002 488080000 &&& gm (wpm2 487088190 991810) (P10k.take 278) =
    wem 487088190 487090002 488080000 := by
  decide +kernel

/-- Window MV167: every even n in [488080002, 489070000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v167 : wem 488078190 488080002 489070000 &&& gm (wpm2 488078190 991810) (P10k.take 278) =
    wem 488078190 488080002 489070000 := by
  decide +kernel

/-- Window MV168: every even n in [489070002, 490060000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v168 : wem 489068190 489070002 490060000 &&& gm (wpm2 489068190 991810) (P10k.take 278) =
    wem 489068190 489070002 490060000 := by
  decide +kernel

/-- Window MV169: every even n in [490060002, 491050000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v169 : wem 490058190 490060002 491050000 &&& gm (wpm2 490058190 991810) (P10k.take 278) =
    wem 490058190 490060002 491050000 := by
  decide +kernel

/-- Window MV170: every even n in [491050002, 492040000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v170 : wem 491048190 491050002 492040000 &&& gm (wpm2 491048190 991810) (P10k.take 278) =
    wem 491048190 491050002 492040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
