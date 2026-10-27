/-
P0069 Baker, Harman, Pintz 1997, Lemma 34, pages 49 and 50, read from the page images
papers/P0069-original.pdf. Unit U-5154, CLOUD 20261019T0213Z-cloud14.

Exponents of `Y`; `n ≤ Y^{1/2 + θ₂/4 - 2ε}`, `p₁ < Y^{c₁}`.
PROVED, the exponent steps of the proof: after `j` steps with `p₁⋯p_{j-1} ≤ Y^ε` and `p_j ≤ p_{j-1}`, `p₁⋯p_j ≤ Y^{2ε}`; and if
`p₁⋯p_j ≤ Y^ε` then `np₁⋯p_j ≤ Y^{1/2 + θ₂/4 - ε}`, the bound of the Lemma 35 note. All MATCH.
That `P ≥ Y^ε` with `p₁ < Y^{c₁}` is case (5.13) of Lemma 33 is immediate from the definitions
and is not a theorem here; an earlier `big_P` restated its hypotheses and was removed after VERIFY.
The Buchstab identity, Lemma 5 and Lemma 30 inputs are not formalized here.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the kernel.
-/
import Mathlib

namespace LeanLab.BHP1997.Lemma34

/-- `p₁⋯p_{j-1} ≤ Y^ε` and `p_j ≤ p_{j-1} ≤ p₁⋯p_{j-1}` give `p₁⋯p_j ≤ Y^{2ε}`. -/
theorem prod_le {s pj pprev ε : ℝ} (hs : s ≤ ε) (hj : pj ≤ pprev) (hprev : pprev ≤ s) :
    s + pj ≤ 2 * ε := by linarith

/-- `n ≤ Y^{1/2 + θ₂/4 - 2ε}`, `p₁⋯p_j ≤ Y^ε`: `np₁⋯p_j ≤ Y^{1/2 + θ₂/4 - ε}`. -/
theorem np_le {n s th2 ε : ℝ} (hn : n ≤ 1 / 2 + th2 / 4 - 2 * ε) (hs : s ≤ ε) :
    n + s ≤ 1 / 2 + th2 / 4 - ε := by linarith

end LeanLab.BHP1997.Lemma34
