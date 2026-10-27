/-
P0070, pp. 363 and 367, the actual modulus family used in the minor arc decomposition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Decomp97
import LeanLab.PerelliPintz1992.ConductorBlocks97

namespace LeanLab.PerelliPintz1992.Decomp97
open Real Finset
open LeanLab.PerelliPintz1992.Section6
noncomputable section
attribute [local instance] Classical.propDecidable

attribute [-instance] Finset.decidableExistsAndFinsetCoe Finset.decidableExistsAndFinset in
/-- LEAF. Page 363: choose one reduced Farey centre for each actual modulus in Y.
Its positive reduced denominator is exactly that modulus. -/
theorem Y_farey_family (N : ℕ) (ε ξ : ℝ) (M : ℕ) :
    ∃ F : Finset ℚ, fareyWindowModuli F = Y N ε ξ M ∧
      (∀ x ∈ F, M ≤ x.den ∧ x.den ≤ 2 * M) ∧
      (∀ x ∈ F, ∃ α : ℝ,
        |(x : ℝ) - α| ≤ 1 / ((x.den : ℝ) * Q N) ∧ |α - ξ| ≤ 1 / H N ε) := by
  classical
  have hchoose : ∀ q : Y N ε ξ M, ∃ x : ℚ, x.den = (q.val : ℕ) ∧
      ∃ α : ℝ, |(x : ℝ) - α| ≤ 1 / ((q.val : ℝ) * Q N) ∧ |α - ξ| ≤ 1 / H N ε := by
    intro q
    obtain ⟨_, _, a, ha, hcop, α, hα, hξ⟩ := ((@Finset.mem_filter _ _ _ _ _).mp q.property).2
    let x : ℚ := (a : ℚ) / (q.val : ℕ)
    have hden : x.den = (q.val : ℕ) := by
      have hh := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := ((q.val : ℕ) : ℤ))
        (by exact_mod_cast q.val.property) (by simpa using hcop)
      change (x.den : ℤ) = (q.val : ℕ) at hh
      exact Int.ofNat_injective hh
    refine ⟨x, hden, α, ?_, hξ.le⟩
    simpa only [x, Rat.cast_div, Rat.cast_natCast, abs_sub_comm] using hα
  choose x hxden hxmeet using hchoose
  let F := Finset.univ.image x
  refine ⟨F, ?_, ?_, ?_⟩
  · ext q
    constructor
    · intro hq
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hq
      obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.mp hu
      have hd : (⟨(x q₀).den, (x q₀).pos⟩ : ℕ+) = q₀.val := Subtype.ext (hxden q₀)
      rw [hd] at heq
      exact heq ▸ q₀.property
    · intro hq
      apply Finset.mem_image.mpr
      refine ⟨x ⟨q, hq⟩, Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_univ _, rfl⟩, ?_⟩
      exact Subtype.ext (hxden ⟨q, hq⟩)
  · intro u hu
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
    rw [hxden q]
    exact ⟨((@Finset.mem_filter _ _ _ _ _).mp q.property).2.1, ((@Finset.mem_filter _ _ _ _ _).mp q.property).2.2.1⟩
  · intro u hu
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [hxden q] using hxmeet q

/-- LEAF. Page 363, equation 21 for the actual Y of the decomposition, uniformly in xi. -/
theorem Y_card_le (N : ℕ) (hN : 0 < N) (ε ξ : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (hMQ : (M : ℝ) ≤ Q N) :
    ((Y N ε ξ M).card : ℝ) ≤ 9 * ((M : ℝ) ^ 2 / H N ε + 1) := by
  obtain ⟨F, hF, hden, hmeet⟩ := Y_farey_family N ε ξ M
  have hH : 0 < H N ε := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hc : ((Y N ε ξ M).card : ℝ) ≤ (F.card : ℝ) := by
    rw [← hF]
    exact_mod_cast (show (fareyWindowModuli F).card ≤ F.card from Finset.card_image_le)
  exact hc.trans (farey_arcs_card_le F M hM (Q N) (H N ε) ξ hMQ hH hden hmeet)

/-- LEAF. Page 367, equation 37 for the actual modulus family of the decomposition. -/
theorem Y_conductors_bound (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ ε ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
      (M : ℝ) ≤ Q N →
      ((characterConductors (Y N ε ξ M)).card : ℝ) ≤
        C * ((M : ℝ) ^ 2 / H N ε + 1) * (M : ℝ) ^ ν := by
  obtain ⟨C, hC, hbound⟩ := farey_window_conductors ν hν
  refine ⟨C, hC, ?_⟩
  intro N hN ε ξ M hM hMQ
  obtain ⟨F, hF, hden, hmeet⟩ := Y_farey_family N ε ξ M
  rw [← hF]
  exact hbound F M hM (Q N) (H N ε) ξ hMQ
    (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hden hmeet

end
end LeanLab.PerelliPintz1992.Decomp97
