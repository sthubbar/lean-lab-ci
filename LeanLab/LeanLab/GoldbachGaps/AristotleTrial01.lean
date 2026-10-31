/-
Aristotle trial 1, lean-aristotle 2026-10-24. Triad 09 target, folder GoldbachGaps: the natural
number form of `goldbach_gaps`, consecutive Goldbach numbers g < g' have
g' - g <= max 2 (g / 36082897) + 6, CONDITIONAL ON the cited inputs hE and h1 exactly as
`goldbach_gaps` in Unconditional.lean takes them.
Statement copied from triad09 attempt b, Triad09.lean on gemini/verify-v03-11033162954838274615,
unchanged; renamed namespace only. Proof written by Aristotle, Harmonic, project
97eb2be2-6b89-4f1d-a50b-8aaa9e57ac0b, on Lean 4.28; checked by lean-aristotle on Lean and
Mathlib 4.35 against a standalone copy with the same definitions inlined: builds, axioms
propext, Classical.choice, Quot.sound only, statement sha256 unchanged. This repo file itself
is NOT yet built: the lean-refresh merge rebuild is the trusted check. AI wrote the Lean code.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.KadiriLumley2014.Statements
import LeanLab.GoldbachGaps.Unconditional

namespace LeanLab.GoldbachGaps.AristotleTrial01
open Real LeanLab.KadiriLumley2014 LeanLab.GoldbachGaps

theorem triad09_main (hE : EvenGoldbachUpTo (4 * 10 ^ 18)) (h1 : KLRow (4 * 10 ^ 18) 36082898)
    (g g' : ℕ) (hg : IsGoldbachNumber g) (_hg' : IsGoldbachNumber g') (_hlt : g < g')
    (h_next : ∀ n, g < n → n < g' → ¬IsGoldbachNumber n) :
    (g' : ℝ) - (g : ℝ) ≤ max 2 ((g : ℝ) / 36082897) + 6 := by
  obtain ⟨hgE, p0, q0, hp0, hq0, hpq0⟩ := hg
  have hg4 : 4 ≤ g := by have := hp0.two_le; have := hq0.two_le; omega
  by_cases hsmall : g' ≤ g + 2
  · have : (g' : ℝ) ≤ g + 2 := by exact_mod_cast hsmall
    have : (2:ℝ) ≤ max 2 ((g : ℝ) / 36082897) := le_max_left _ _
    linarith
  · push_neg at hsmall
    have hbig : 4 * 10 ^ 18 < g + 2 := by
      by_contra hc
      push_neg at hc
      exact h_next (g + 2) (by omega) hsmall
        ⟨hgE.add (by decide), hE _ (hgE.add (by decide)) (by omega) hc⟩
    have hg'big : 4 * 10 ^ 18 + 3 < g' := by
      obtain ⟨k, hk⟩ := _hg'.1
      obtain ⟨j, hj⟩ := hgE
      omega
    obtain ⟨p, hp, hlo, hhi⟩ := h1 ((g' : ℝ) - 3) (by
      have : ((4 * 10 ^ 18 + 3 : ℕ) : ℝ) < g' := by exact_mod_cast hg'big
      push_cast at this; linarith)
    have hp3 : p + 3 < g' := by
      have : (p : ℝ) + 3 < g' := by linarith
      exact_mod_cast this
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : ((4 * 10 ^ 18 + 3 : ℕ) : ℝ) < g' := by exact_mod_cast hg'big
      push_cast at this hlo
      norm_num at hlo
      linarith
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hle : p + 3 ≤ g := by
      by_contra hc
      push_neg at hc
      exact h_next (p + 3) hc hp3
        ⟨hpodd.add_odd (by decide), p, 3, hp, Nat.prime_three, rfl⟩
    have hle' : (p : ℝ) + 3 ≤ g := by exact_mod_cast hle
    have : (g : ℝ) / 36082897 ≤ max 2 ((g : ℝ) / 36082897) := le_max_right _ _
    norm_num at hlo
    linarith

end LeanLab.GoldbachGaps.AristotleTrial01
