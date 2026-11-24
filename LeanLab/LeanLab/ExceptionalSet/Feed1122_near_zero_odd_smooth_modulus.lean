import LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_odd_index
import LeanLab.ExceptionalSet.Feed1122_near_zero_even_smooth_modulus

/-!
Feed split of `leaf_near_zero_odd_smooth_modulus` of
`LeanLab.ExceptionalSet.SPLIT_leaf_near_zero_odd_index`.

Source: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier
48 (1998), P0082, page 358, displays 9 and 10.  As in the even case, the smooth conductor
range is empty for large `N`: a primitive real character whose modulus has only the prime
factors two and three has modulus dividing `24`, and such a character has no real zero in
`[1 - a / log P, 1)` once `P` is large.

The one leaf is shared with the even case and lives in
`LeanLab.ExceptionalSet.Feed1122_near_zero_even_smooth_modulus`:
`leaf_quadratic_primitive_smooth_conductor_dvd_24`, MEDIUM.  The analytic input
`feed1122_small_conductor_no_real_zero_near_one` is proved there.  This file proves the odd index target
from them through the proved helper `feed1122_smooth_selected_trivial`; the remaining case
`r = 1` contradicts `1 < Int.gcd (nu γ n + 1) r`.

AI wrote the Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp559b

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- Assembly, statement copied verbatim from `leaf_near_zero_odd_smooth_modulus`. -/
theorem leaf_near_zero_odd_smooth_modulus_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (a : ℝ) (ha : 0 < a) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            SelectedRealZero a (F γ N ^ (6 * δ)) r →
            (∀ p : ℕ, p.Prime → p ∣ r → p ≤ 3) →
            ∀ n ∈ window γ N, ¬ Even (nu γ n) →
              ((nu γ n + 1 : ℤ) : ℝ) ≤ F γ N →
              1 < Int.gcd (nu γ n + 1) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + 1) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                  (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re +
                    A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + 1) := by
  refine ⟨1, one_pos, fun δ hδ _ => ⟨1, one_pos, fun κ _ _ => ⟨1, 1, one_pos, one_pos, ?_⟩⟩⟩
  obtain ⟨N₀, hN₀⟩ := feed1122_smooth_selected_trivial γ h1 a ha δ hδ
  refine ⟨N₀, fun N hN r _ _ hsel hsmooth n _ _ _ hgcd _ _ => ?_⟩
  exfalso
  have hr1 := hN₀ N hN r hsel hsmooth
  subst hr1
  simp at hgcd

end LeanLab.ExceptionalSet.UpJ200.Decomp559b
