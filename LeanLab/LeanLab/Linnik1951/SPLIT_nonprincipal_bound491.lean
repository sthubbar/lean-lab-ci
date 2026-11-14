/-
The nonprincipal character block of the local major arc integral at an integer
residual, cut into three steps: the number of nonprincipal characters of the
modulus, the pairs of characters whose product is principal, and the pairs of
characters whose product is not principal.

The block is the double sum of the ordered character pair contribution over the
nonprincipal characters of the modulus. Summing over the second character index
first, for a fixed nonprincipal character, splits that inner sum into the pairs
whose product is the principal character and the pairs whose product is not: the
first group carries the full reduced residue phase and the second is where the
character square saves a factor of the modulus. Counting the nonprincipal
characters then multiplies the one-index bound by at most the totient, which is
what removes the modulus from the final bound.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- LEAF. Step one of the nonprincipal block, the counting step. The nonprincipal
characters of a positive modulus number at most the totient of the modulus, so
the outer sum of the block has at most that many terms. -/
theorem nonprincipal_character_count491 (q : ℕ) (hq : 1 ≤ q) :
    letI : NeZero q := ⟨by omega⟩
    (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have hcard : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at hcard
  have hle := Finset.card_filter_le (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => χ ≠ 1)
  simpa [hcard] using hle

/-- The principal-product filter for a fixed nonprincipal character contains
exactly its inverse. -/
theorem nonprincipal_principal_filter491 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
        (fun ψ => ψ * χ = 1) = {χ⁻¹} := by
  classical
  ext ψ
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hmul⟩
    refine ⟨eq_inv_of_mul_eq_one_left hmul, ?_⟩
    intro hinv
    exact hχ (inv_eq_one.mp hinv)
  · rintro ⟨-, rfl⟩
    simp

/-- LEAF. Step two of the nonprincipal block, the pairs with a principal product,
for one fixed nonprincipal character. The reduced residue phase of such a pair is
an untwisted Ramanujan phase, bounded by the residue count, so this block of
pairs is bounded with one factor of the totient in the denominator and without
any character square saving. -/
theorem nonprincipal_principal_product491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1),
            characterPair491 N q n χ ψ‖ ≤
            C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := by
  sorry

/-- LEAF. Step three of the nonprincipal block, the pairs with a nonprincipal
product, for one fixed nonprincipal character. Here the twisted reduced residue
phase is a character sum of nonprincipal product, and the character square
estimate saves the factor of the modulus needed for modulus uniformity, so this
block also carries one factor of the totient in the denominator. -/
theorem nonprincipal_off_product491 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1),
            characterPair491 N q n χ ψ‖ ≤
            C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := by
  sorry

/-- The nonprincipal block, assembled from the two one-index estimates and the
character count. Each fixed nonprincipal character contributes its principal
product block and its nonprincipal product block, both bounded by the same
quantity, and there are at most a totient of such characters, so the totient
cancels and the modulus disappears from the bound. -/
theorem nonprincipal_bound491_split (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖nonprincipalTerm491 N q n‖ ≤
          C * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
  obtain ⟨C1, hC1, N1, h1⟩ := nonprincipal_principal_product491 hM
  obtain ⟨C2, hC2, N2, h2⟩ := nonprincipal_off_product491 hM
  refine ⟨C1 + C2, add_pos hC1 hC2, max N1 (max N2 1), ?_⟩
  intro N hN q hq hqQ n
  letI : NeZero q := ⟨by omega⟩
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNs : max N2 1 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_left _ _) hNs
  have hNgt : 1 < N := lt_of_le_of_lt (le_max_right N2 1) hNs
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hτ : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega))
  have hCpos : (0 : ℝ) < C1 + C2 := add_pos hC1 hC2
  have hX : 0 ≤ (C1 + C2) *
      ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
    apply div_nonneg
    · apply mul_nonneg hCpos.le
      exact mul_nonneg (div_nonneg hNpos.le hτ.le) (pow_nonneg hlog 13)
    · exact hφpos.le
  have hmain : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖ ≤
        (C1 + C2) *
          ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
    intro χ hχne
    have hA := h1 N hN1 q hq hqQ n χ hχne
    have hB := h2 N hN2 q hq hqQ n χ hχne
    have hsplit : (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
            (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ) +
          (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
            (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ) =
        ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    calc ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖
        = ‖(∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ) +
            (∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ)‖ := by
          rw [hsplit]
      _ ≤ ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ = 1), characterPair491 N q n χ ψ‖ +
            ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)).filter
              (fun ψ => ψ * χ ≠ 1), characterPair491 N q n χ ψ‖ := norm_add_le _ _
      _ ≤ C1 * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) +
            C2 * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 /
              (q.totient : ℝ) := add_le_add hA hB
      _ = (C1 + C2) *
          ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) / (q.totient : ℝ) := by
          ring
  change ‖∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
      ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
        characterPair491 N q n χ ψ‖ ≤
    (C1 + C2) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13
  calc ‖∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
        ∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
          characterPair491 N q n χ ψ‖
      ≤ ∑ χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          ‖∑ ψ ∈ (univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)),
            characterPair491 N q n χ ψ‖ := norm_sum_le _ _
    _ ≤ ∑ _χ ∈ (univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)),
          (C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ) := by
        apply Finset.sum_le_sum
        intro χ hχ
        exact hmain χ (by simpa using hχ)
    _ = ((univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          ((C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q.totient : ℝ) *
          ((C1 + C2) *
            ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) /
              (q.totient : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hX
        exact_mod_cast (nonprincipal_character_count491 q hq)
    _ = (C1 + C2) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13) := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hφpos.ne'
    _ = (C1 + C2) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 13 := by
        ring

end LeanLab.Linnik1951
