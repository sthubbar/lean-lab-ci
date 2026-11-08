import LeanLab.ExceptionalSet.GammaMean465
import LeanLab.ExceptionalSet.GammaTwoMean465

/-!
The infinite divisor error left in P0082 pages361 and362, Lemma5.
The finite Gamma1 average is supplied from the explicit discrepancy input.
The infinite Gamma2 average is supplied from that same explicit input.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page359 display15, the positive envelope for Gamma2. -/
noncomputable def gammaTwo (r : ℕ) (P : ℝ) (m : ℤ) : ℝ :=
  (r : ℝ) * ∑' q : ℕ, if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd m q).totient : ℝ)) else 0

/-- LEAF. P0082 pages361 and362 displays17 to19, only the infinite Gamma2
average from Lemma5. CONDITIONAL ON cited Lemma4. It contains no finite Gamma1 sum, no major coefficient,
no exceptional count and no pointwise major arc expansion. -/
theorem leaf_gammaTwo_mean (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N, gammaTwo r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  simpa only [gammaTwo] using
    gammaTwo_mean_from_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2

/-- P0082 page362, completion of Lemma5. The finite and infinite divisor
errors add. CONDITIONAL ON the new infinite mean leaf and the cited Lemma4.
The result unfolds to the exact full divisorError mean statement. -/
theorem error_mean_from_parts (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                (gammaOne r (F γ N ^ (6 * δ)) (nu γ n + j) +
                  gammaTwo r (F γ N ^ (6 * δ)) (nu γ n + j)) ≤
                    C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨δa, hδa, ha⟩ := gammaOne_mean_from_lemma4 LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_gammaTwo_mean γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ca, hCa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Cb, hCb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ca + Cb, add_pos hCa hCb, max Na Nb, fun N hN r hr hrP j hj => ?_⟩
  rw [sum_add_distrib]
  have haN := ha N ((le_max_left _ _).trans hN) r hr hrP j hj
  have hbN := hb N ((le_max_right _ _).trans hN) r hr hrP j hj
  calc
    _ ≤ Ca * N * calE γ κ N ^ (-(1 / 2 : ℝ)) +
        Cb * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := add_le_add haN hbN
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
