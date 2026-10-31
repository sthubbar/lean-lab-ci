/-
U-1430, PC run 20261021T1403Z-5629, track T2, idea I-0102.

Kim 2024 P0057 Theorem 1.2 fed by the 7/8 half-plane.

* `zeroFree_of_H78`: PROVED. `HalfPlane78 → ZeroFreeAssumption` with `c₂ = 1/8`.
  No mismatch is lost: both range over every modulus `q` with `[NeZero q]`, every `χ` and every
  `s`; `HalfPlane78` excludes only the pair `χ = 1 ∧ s = 1`, while `ZeroFreeAssumption` excludes
  every `s = 1`, so `HalfPlane78` is the stronger hypothesis there.
* `halfPlane78_iff_zeroFreeWith`: PROVED. `HalfPlane78` is EQUIVALENT to the zero-free strip with
  the explicit constant `c₂ = 1/8`; the extra point `s = 1, χ ≠ 1` is Mathlib's unconditional
  `L(1, χ) ≠ 0`.
* `halfPlane78_iff_forall_Q`: PROVED. The modulus-bounded `Ternary78.Threshold.HalfPlane78 Q`
  for every `Q` is equivalent to the unbounded one. A single fixed `Q` is weaker: it says nothing
  about moduli above `Q`, and `HalfPlane78 0` holds vacuously, `halfPlaneQ_zero`.
* `kim_of_H78`: CONDITIONAL ON `HalfPlane78`, OpenAI 30 Sep 2026, unrefereed, AND on the cited
  `kim_thm1_2`, which is stated with `sorry`, so its axioms show `sorryAx`. Kim has also said the
  minor arc treatment of Theorem 1.2 needs an erratum, see PROGRESS.md.
* Vacuity: `HalfPlane78` cannot be instantiated in Lean; it is a research claim. What is checked:
  its `Re s ≥ 1` part holds unconditionally, `halfPlane_re_ge_one`, and its hypotheses are met at
  `q = 1, χ = 1, s = 2`, `GoldbachShort78.halfPlane78_instance`, where the conclusion `ζ(2) ≠ 0`
  is proved here, `vacuity_s2`.

AI-written Lean code, Claude, U-1430. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.MissingDigit.Statements
import LeanLab.GoldbachShort78.Statements
import LeanLab.Ternary78.Threshold

namespace LeanLab.MissingDigit.U1430

open LeanLab.MissingDigit
open LeanLab.GoldbachShort78 (HalfPlane78)

/-- The zero-free strip `Re s > 1 - c₂` with an explicit constant, the body of
`ZeroFreeAssumption`. -/
def ZeroFreeWith (c₂ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    1 - c₂ < s.re → s ≠ 1 → DirichletCharacter.LFunction χ s ≠ 0

theorem zeroFreeAssumption_iff : ZeroFreeAssumption ↔ ∃ c₂ : ℝ, 0 < c₂ ∧ ZeroFreeWith c₂ :=
  Iff.rfl

/-- PROVED: the half-plane gives the strip with `c₂ = 1/8`. -/
theorem zeroFreeWith_of_H78 (h : HalfPlane78) : ZeroFreeWith (1 / 8) := by
  intro q _ χ s hs hs1
  exact h q χ s (by linarith) (Or.inr hs1)

/-- PROVED: `HalfPlane78 → ZeroFreeAssumption`, witness `c₂ = 1/8`. -/
theorem zeroFree_of_H78 (h : HalfPlane78) : ZeroFreeAssumption :=
  ⟨1 / 8, by norm_num, zeroFreeWith_of_H78 h⟩

/-- PROVED, unconditional: the `Re s ≥ 1` part of `HalfPlane78`, from Mathlib. -/
theorem halfPlane_re_ge_one : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    1 ≤ s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro q _ χ s hs hχs
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

/-- PROVED: `HalfPlane78` is equivalent to the strip with `c₂ = 1/8`; nothing is lost. -/
theorem halfPlane78_iff_zeroFreeWith : HalfPlane78 ↔ ZeroFreeWith (1 / 8) := by
  refine ⟨zeroFreeWith_of_H78, fun h q _ χ s hs hχs => ?_⟩
  by_cases hs1 : s = 1
  · exact halfPlane_re_ge_one q χ s (by simp [hs1]) hχs
  · exact h q χ s (by linarith) hs1

/-- PROVED: the bounded-modulus version for every `Q` is the unbounded `HalfPlane78`. -/
theorem halfPlane78_iff_forall_Q :
    HalfPlane78 ↔ ∀ Q : ℕ, LeanLab.Ternary78.Threshold.HalfPlane78 Q := by
  constructor
  · intro h Q q _ _ χ s hs hχs
    exact h q χ s hs hχs
  · intro h q _ χ s hs hχs
    exact h q q le_rfl χ s hs hχs

/-- PROVED: a single bounded `Q` is weak; at `Q = 0` it holds vacuously. -/
theorem halfPlaneQ_zero : LeanLab.Ternary78.Threshold.HalfPlane78 0 := by
  intro q hq hq0
  exact absurd (Nat.le_zero.mp hq0) (NeZero.ne q)

/-- PROVED: from the bounded family. -/
theorem zeroFree_of_forall_Q (h : ∀ Q : ℕ, LeanLab.Ternary78.Threshold.HalfPlane78 Q) :
    ZeroFreeAssumption :=
  zeroFree_of_H78 (halfPlane78_iff_forall_Q.mpr h)

/-- **CONDITIONAL ON `HalfPlane78` AND on the cited `kim_thm1_2`**, which carries `sorry`. -/
theorem kim_of_H78 (h : HalfPlane78) : AlmostAllGoldbach (2 / 3) :=
  kim_thm1_2 (zeroFree_of_H78 h)

/-- Vacuity: at `q = 1, χ = 1, s = 2` the hypotheses of `HalfPlane78` hold and so does its
conclusion, unconditionally. -/
theorem vacuity_s2 : (7 : ℝ) / 8 < (2 : ℂ).re ∧
    ((1 : DirichletCharacter ℂ 1) ≠ 1 ∨ (2 : ℂ) ≠ 1) ∧
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) 2 ≠ 0 := by
  refine ⟨by norm_num, Or.inr (by norm_num), ?_⟩
  exact halfPlane_re_ge_one 1 1 2 (by norm_num) (Or.inr (by norm_num))

end LeanLab.MissingDigit.U1430
