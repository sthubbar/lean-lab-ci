/-
Source: Prove2Me https://beta.prove2.me.
Mission: 961d4484.
Theorem: LL_Decomp587f.r3Nine_short.
Author: kmehltretter82.
Accepted: 2026-11-19.
Theorem id: bfe82e33-9c35-44d6-ad7a-fd2d81392447.
Submission id: a058b49a-7607-495f-8498-3847893ae209.
License: Apache 2.0 per Prove2Me terms.
Source environment: Lean 4.33.1.
Port environment: Lean 4.35.
Use the lab definitions and existing Mathlib ceiling division lemma.
Build and axiom evidence is recorded in the task log.
AI adapted the Lean code. Binary Goldbach is open.
-/
import LeanLab.ChenDoubleSieve.I2Range
import LeanLab.Ported.Prove2Me.Decomp587fR3NineSub0
import LeanLab.Ported.Prove2Me.Decomp587fR3NineSub1
import LeanLab.Ported.Prove2Me.Decomp587fR3NineSub2
import LeanLab.Ported.Prove2Me.Decomp587fR3NineSub3

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanLab.Ported.Prove2Me.Decomp587fR3NineShort

open Real Set MeasureTheory
open LeanLab.ChenDoubleSieve LeanLab.ChenDoubleSieve.Wu04Functional

theorem solution {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {φ : ℝ} (hφ : 2 ≤ φ) (hφtop : φ ≤ (13 / 5 : ℝ)) :
    buchstabIntegral ω 1 (fun _ => (25 / 89 : ℝ)) (fun _ => (2 / 5 : ℝ)) φ ≤
      (12408337 / 1000000000 : ℝ) := by
  by_cases h0 : φ ≤ (649 / 320 : ℝ)
  · exact LeanLab.Ported.Prove2Me.Decomp587fR3NineSub0.solution hω hz hφ h0
  · by_cases h1 : φ ≤ (1307 / 640 : ℝ)
    · exact LeanLab.Ported.Prove2Me.Decomp587fR3NineSub1.solution hω hz (le_of_not_ge h0) h1
    · by_cases h2 : φ ≤ (329 / 160 : ℝ)
      · exact LeanLab.Ported.Prove2Me.Decomp587fR3NineSub2.solution hω hz (le_of_not_ge h1) h2
      · exact LeanLab.Ported.Prove2Me.Decomp587fR3NineSub3.solution hω hz (le_of_not_ge h2) hφtop

end LeanLab.Ported.Prove2Me.Decomp587fR3NineShort
