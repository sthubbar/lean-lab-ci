/-
Kim 2024, P0057, the author's fix for F-0007, reply of 2026-10-19 by J. Kim:
replace I₁ = (X − H, X] by I₁ = [X − H, X + H], keeping I₂ = (0, H].
With the fixed I₁, M*(m) = #{(h, k) ∈ I₁ × I₂ : h + k = m} equals H exactly for every
m with X ≤ m ≤ X + H and H ≤ X, so the claim M*(2n) ≍ H of section 1.3 holds
uniformly on [X, X+H], the top end included. Vacuity: at X = 100, H = 10, m = X + H the
printed M* is 1, the fixed one is 10.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.MissingDigit.KimMainTerm

namespace LeanLab.MissingDigit

open Finset

/-- The author's fixed count: `I₁ = [X − H, X + H]`, `I₂ = (0, H]`. -/
def MstarFixed (X H m : ℕ) : ℕ :=
  ((Icc (X - H) (X + H) ×ˢ Ioc 0 H).filter (fun p => p.1 + p.2 = m)).card

/-- With the fixed `I₁`, every `k ∈ (0, H]` gives a representation of any `m ∈ [X, X+H]`. -/
theorem MstarFixed_eq {X H m : ℕ} (hHX : H ≤ X) (hXm : X ≤ m) (hm : m ≤ X + H) :
    MstarFixed X H m = H := by
  unfold MstarFixed
  have hset : ((Icc (X - H) (X + H) ×ˢ Ioc 0 H).filter (fun p => p.1 + p.2 = m)) =
      (Ioc 0 H).image (fun k => (m - k, k)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ioc,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      exact ⟨p.2, ⟨h3, h4⟩, Prod.ext (by simp; omega) rfl⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨⟨by omega, by omega⟩, hk1, hk2⟩, show m - k + k = m by omega⟩
  rw [hset, Finset.card_image_of_injective _ (fun a b h => (Prod.ext_iff.mp h).2)]
  simp

/-- The fixed count is never more than `H`. -/
theorem MstarFixed_le (X H m : ℕ) : MstarFixed X H m ≤ H := by
  unfold MstarFixed
  calc _ ≤ ((Ioc 0 H).image (fun k => (m - k, k))).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_Ioc] at hp
        rw [Finset.mem_image]
        exact ⟨p.2, Finset.mem_Ioc.mpr hp.1.2, Prod.ext (by simp; omega) rfl⟩
    _ ≤ (Ioc 0 H).card := Finset.card_image_le
    _ = H := by simp

/-- At the top end the printed count is `1` and the fixed count is `H`. -/
theorem fix_at_top {X H : ℕ} (hH : 1 ≤ H) (hHX : H ≤ X) :
    Mstar X H (X + H) = 1 ∧ MstarFixed X H (X + H) = H :=
  ⟨Mstar_top hH hHX, MstarFixed_eq hHX (by omega) le_rfl⟩

/-- Vacuity instance: `X = 100`, `H = 10`. -/
example : Mstar 100 10 110 = 1 ∧ MstarFixed 100 10 110 = 10 := fix_at_top (by norm_num) (by norm_num)

/-- **F-0007 fixed as the author proposes**: on the even elements of `[X, X+H]*` for
`X = g^k`, `H = g^j`, `1 ≤ j < k`, the fixed count is exactly `H`; in particular the top
element `X + H` that breaks the printed version now has count `H`. -/
theorem fixed_at_top_mem {g b j k : ℕ} (hg : 2 ≤ g) (hb : 2 ≤ b) (hj : 1 ≤ j) (hjk : j < k) :
    g ^ k + g ^ j ∈ (starSet g b (g ^ k) ((g ^ j : ℕ) : ℝ)).filter Even ∧
      MstarFixed (g ^ k) (g ^ j) (g ^ k + g ^ j) = g ^ j :=
  ⟨top_mem hg hb hj hjk,
    MstarFixed_eq (Nat.pow_lt_pow_right (by omega) hjk).le (by omega) le_rfl⟩

end LeanLab.MissingDigit
