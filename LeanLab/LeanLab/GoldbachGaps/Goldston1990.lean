/-
P0030 Goldston 1990 page 285. The two quoted RH consequences now use the existing
Goldston1990RH proofs. Shared declarations live in Goldston1990Base with identical text.
Both results are conditional on RiemannHypothesis only.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.GoldbachGaps.Goldston1990RH

namespace LeanLab.GoldbachGaps.Goldston1990

/-- Linnik under RH, as quoted on page 285. -/
theorem linnik : RiemannHypothesis → LinnikRH := by
  exact linnik_proved

/-- Kátai, Montgomery and Vaughan under RH, as quoted on page 285. -/
theorem kataiMV : RiemannHypothesis → KataiMV := by
  exact kataiMV_proved

end LeanLab.GoldbachGaps.Goldston1990
