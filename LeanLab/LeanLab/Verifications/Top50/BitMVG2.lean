/-
Kernel Goldbach windows MV11 to MV20, width 990000, even n in [333640002, 343540000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV11: every even n in [333640002, 334630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v11 : wem 333638190 333640002 334630000 &&& gm (wpm2 333638190 991810) (P10k.take 278) =
    wem 333638190 333640002 334630000 := by
  decide +kernel

/-- Window MV12: every even n in [334630002, 335620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v12 : wem 334628190 334630002 335620000 &&& gm (wpm2 334628190 991810) (P10k.take 278) =
    wem 334628190 334630002 335620000 := by
  decide +kernel

/-- Window MV13: every even n in [335620002, 336610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v13 : wem 335618190 335620002 336610000 &&& gm (wpm2 335618190 991810) (P10k.take 278) =
    wem 335618190 335620002 336610000 := by
  decide +kernel

/-- Window MV14: every even n in [336610002, 337600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v14 : wem 336608190 336610002 337600000 &&& gm (wpm2 336608190 991810) (P10k.take 278) =
    wem 336608190 336610002 337600000 := by
  decide +kernel

/-- Window MV15: every even n in [337600002, 338590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v15 : wem 337598190 337600002 338590000 &&& gm (wpm2 337598190 991810) (P10k.take 278) =
    wem 337598190 337600002 338590000 := by
  decide +kernel

/-- Window MV16: every even n in [338590002, 339580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v16 : wem 338588190 338590002 339580000 &&& gm (wpm2 338588190 991810) (P10k.take 278) =
    wem 338588190 338590002 339580000 := by
  decide +kernel

/-- Window MV17: every even n in [339580002, 340570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v17 : wem 339578190 339580002 340570000 &&& gm (wpm2 339578190 991810) (P10k.take 278) =
    wem 339578190 339580002 340570000 := by
  decide +kernel

/-- Window MV18: every even n in [340570002, 341560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v18 : wem 340568190 340570002 341560000 &&& gm (wpm2 340568190 991810) (P10k.take 278) =
    wem 340568190 340570002 341560000 := by
  decide +kernel

/-- Window MV19: every even n in [341560002, 342550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v19 : wem 341558190 341560002 342550000 &&& gm (wpm2 341558190 991810) (P10k.take 278) =
    wem 341558190 341560002 342550000 := by
  decide +kernel

/-- Window MV20: every even n in [342550002, 343540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v20 : wem 342548190 342550002 343540000 &&& gm (wpm2 342548190 991810) (P10k.take 278) =
    wem 342548190 342550002 343540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
