/-
Kernel Goldbach windows V291 to V300, width 990000, covering even n in [610840002, 620740000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V291: every even n in [610840002, 611830000] is p + q, q among the first 280 primes. -/
theorem window_v291 : wem 610838190 610840002 611830000 &&& gm (wpm2 610838190 991810) (P10k.take 280) =
    wem 610838190 610840002 611830000 := by
  decide +kernel

/-- Window V292: every even n in [611830002, 612820000] is p + q, q among the first 280 primes. -/
theorem window_v292 : wem 611828190 611830002 612820000 &&& gm (wpm2 611828190 991810) (P10k.take 280) =
    wem 611828190 611830002 612820000 := by
  decide +kernel

/-- Window V293: every even n in [612820002, 613810000] is p + q, q among the first 280 primes. -/
theorem window_v293 : wem 612818190 612820002 613810000 &&& gm (wpm2 612818190 991810) (P10k.take 280) =
    wem 612818190 612820002 613810000 := by
  decide +kernel

/-- Window V294: every even n in [613810002, 614800000] is p + q, q among the first 280 primes. -/
theorem window_v294 : wem 613808190 613810002 614800000 &&& gm (wpm2 613808190 991810) (P10k.take 280) =
    wem 613808190 613810002 614800000 := by
  decide +kernel

/-- Window V295: every even n in [614800002, 615790000] is p + q, q among the first 280 primes. -/
theorem window_v295 : wem 614798190 614800002 615790000 &&& gm (wpm2 614798190 991810) (P10k.take 280) =
    wem 614798190 614800002 615790000 := by
  decide +kernel

/-- Window V296: every even n in [615790002, 616780000] is p + q, q among the first 280 primes. -/
theorem window_v296 : wem 615788190 615790002 616780000 &&& gm (wpm2 615788190 991810) (P10k.take 280) =
    wem 615788190 615790002 616780000 := by
  decide +kernel

/-- Window V297: every even n in [616780002, 617770000] is p + q, q among the first 280 primes. -/
theorem window_v297 : wem 616778190 616780002 617770000 &&& gm (wpm2 616778190 991810) (P10k.take 280) =
    wem 616778190 616780002 617770000 := by
  decide +kernel

/-- Window V298: every even n in [617770002, 618760000] is p + q, q among the first 280 primes. -/
theorem window_v298 : wem 617768190 617770002 618760000 &&& gm (wpm2 617768190 991810) (P10k.take 280) =
    wem 617768190 617770002 618760000 := by
  decide +kernel

/-- Window V299: every even n in [618760002, 619750000] is p + q, q among the first 280 primes. -/
theorem window_v299 : wem 618758190 618760002 619750000 &&& gm (wpm2 618758190 991810) (P10k.take 280) =
    wem 618758190 618760002 619750000 := by
  decide +kernel

/-- Window V300: every even n in [619750002, 620740000] is p + q, q among the first 280 primes. -/
theorem window_v300 : wem 619748190 619750002 620740000 &&& gm (wpm2 619748190 991810) (P10k.take 280) =
    wem 619748190 619750002 620740000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
