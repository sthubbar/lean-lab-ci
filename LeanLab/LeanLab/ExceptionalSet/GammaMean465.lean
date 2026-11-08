import LeanLab.ExceptionalSet.GammaOne465
import LeanLab.ExceptionalSet.GammaParameters465
import LeanLab.ExceptionalSet.Progressions465

/-!
P0082 page360 Lemma5, the finite Gamma1 first moment.
The remaining analytic input is the paper's discrepancy Lemma4.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page360 Lemma5, the finite Gamma1 envelope on the literal floor
window. CONDITIONAL ON Lemma4 as an explicit input. It includes both
adjacent shifts and has no new admission. -/
theorem gammaOne_mean_from_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N, gammaOne r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmean⟩ := gammaOne_mean_log
  obtain ⟨δ₀, hδ₀, hp⟩ := progression_counts h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hp⟩ := hp δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨A, hA, Np, hp⟩ := hp κ hκ hκsmall
  obtain ⟨Ns, hs⟩ := gammaOne_parameters γ δ κ h1 h2 hδ hκ
  refine ⟨2 * K * A, by positivity, max 16 (max Np Ns), fun N hN r hr hrP j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hF : 1 ≤ F γ N := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hP : 1 ≤ F γ N ^ (6 * δ) := Real.one_le_rpow hF (by positivity)
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hprog : ∀ d : ℕ, 1 ≤ d → d ≤ ⌊F γ N ^ (6 * δ)⌋₊ →
      (((window γ N).filter (fun n => (d : ℤ) ∣ nu γ n + j)).card : ℝ) ≤
        A * ((N : ℝ) / d + N / calE γ κ N) := by
    intro d hd hdP
    have hdR : (d : ℝ) ≤ F γ N ^ (6 * δ) :=
      (by exact_mod_cast hdP : (d : ℝ) ≤ ⌊F γ N ^ (6 * δ)⌋₊).trans (Nat.floor_le (by linarith))
    exact hp N hNp d hd hdR j hj
  have hm := hmean (window γ N) (fun n => nu γ n + j) r (F γ N ^ (6 * δ))
    (calE γ κ N) A N hr hP hE hA.le hprog
  calc
    _ ≤ K * A * N * (1 + Real.log (F γ N ^ (6 * δ))) ^ 3 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N) := hm
    _ = (K * A * N) * ((1 + Real.log (F γ N ^ (6 * δ))) ^ 3 *
        ((F γ N ^ (6 * δ)) ^ (-(1 / 2 : ℝ)) + 1 / calE γ κ N)) := by ring
    _ ≤ (K * A * N) * (2 * calE γ κ N ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hs N hNs) (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
