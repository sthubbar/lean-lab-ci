import LeanLab.ExceptionalSet.OddMoment446

/-!
The even coefficient part of the major arc lower bound.
Source: P0082 pages 362 to 364, Lemma 7 and displays 20 to 22.
The odd coefficient moments are reused from Decomp371c.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp446a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.Adjacent446 (evenAdjacent)

/-- LEAF. P0082 pages 362 to 364, the even coefficient bound in the
first sentence of the Lemma 7 proof and its four major arc cases.
Only the even coefficient is estimated. The adjacent odd coefficient
and the final sum are absent. Displays 20 to 22 control its bad indices. -/
theorem leaf_even_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  sorry

/-- Assembly. P0082 page 362, first sentence of the Lemma 7 proof.
This has the exact Decomp371a.leaf_coefficient_lower statement.
It uses the new even leaf and the two inherited odd coefficient moments. -/
theorem coefficient_lower_assembly (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := leaf_even_coefficient_lower γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := OddMoment446.odd_moment_uniform γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, Be, hc, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bo, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c / 2, Be + 16 * Bo / c ^ 2, by positivity, by positivity,
    max 2 (max Ne No), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNo : No ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  let f : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)
  let g : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  let T := c / 2 * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  have hpair := Adjacent446.bad_pair_count (window γ N) f g T
  have hrewrite (n : ℕ) : f n + g n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) :=
    Adjacent446.adjacent_sum (R1 (F γ N ^ (6 * δ)) (F γ N)) γ n
  have htwo : 2 * T = c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    ring
  simp_rw [hrewrite, htwo] at hpair
  have hodd := OddMoment446.odd_bad_count (window γ N) g c Bo (F γ N) (calE γ κ N) N
    hc hBo.le (Real.exp_pos _) hE (ho N hNo)
  have hpairR := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hpairR
  change _ ≤ _ at hodd
  have heN := he N hNe
  change (((window γ N).filter (fun n => (f n).re <
    c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤ _ at heN
  dsimp only [T] at hpairR
  refine hpairR.trans ((add_le_add heN hodd).trans ?_)
  ring_nf
  exact le_rfl

end LeanLab.ExceptionalSet.Decomp446a
