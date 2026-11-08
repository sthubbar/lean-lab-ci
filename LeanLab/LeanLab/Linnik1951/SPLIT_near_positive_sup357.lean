/-
Split of the pointwise supremum bound `near_positive_sup357` on the positive side of
the central interval into smaller steps. Nothing here changes the statement:
`near_positive_sup357_split` repeats it character for character and proves it from the
four OPEN leaves below, which record, in order, (1) the size of the damped character
prime sum at phase zero, (2) its variation between phase zero and phase alpha, (3) the
nonnegativity of the weight N over q times log N to the fifth, and (4) the shortness of
the permitted phase range. The proof of the assembly does not use
`near_positive_sup357`.
-/
import LeanLab.Linnik1951.SPLIT_mellin_near357

namespace LeanLab.Linnik1951

/-- LEAF. Step 1 of 4: the damped character prime sum at phase zero. There is a fixed
positive constant C such that for every large N, every modulus q with 1 at most q at
most N to the one seventh, and every nonprincipal character mod q, the square norm of
the sum at phase zero is at most C times N over q times log N to the fifth. This fixes
the value at one endpoint of the phase range and says nothing about any other phase. -/
theorem near_sup357_origin357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPrime280 χ N 0‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  sorry

/-- LEAF. Step 2 of 4: the variation of the damped character prime sum across the
permitted phase range. There is a fixed positive constant C such that for every large
N, every modulus q with 1 at most q at most N to the one seventh, every nonprincipal
character mod q and every phase alpha between 0 and 4 over N, the square norm of the
difference between the values at alpha and at zero is at most C times the scaled phase
4 alpha N times N over q times log N to the fifth. The scaled phase is the quantity
that step 4 keeps at most 16; at alpha equal to zero the left side is zero and the
bound is immediate. -/
theorem near_sup357_local_variation357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
              C * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  sorry

/-- LEAF. Step 3 of 4: the weight is nonnegative. For N at least one and q at least
one the product of N over q with log N to the fifth is nonnegative. Both estimates of
steps 1 and 2 are multiplied by this weight in the assembly, so its sign is needed
before the two of them are added. -/
theorem near_sup357_weight_nonneg357 {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) :
    (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  sorry

/-- LEAF. Step 4 of 4: the permitted phase range is short. For N at least one and a
phase alpha between 0 and 4 over N, the scaled phase 4 alpha N is at most 16. The
content is that multiplying the phase bound by N gives a bound independent of N; it
carries no character information. -/
theorem near_sup357_phase_length357 {N : ℕ} (hN : 1 ≤ N) {α : ℝ} (hα0 : 0 ≤ α)
    (hαu : α ≤ 4 / (N : ℝ)) :
    4 * α * (N : ℝ) ≤ 16 := by
  sorry

/-- Private helper for the assembly: the square of a norm is at most twice the square
of the norm at a chosen point plus twice the square of the norm of the difference. -/
private lemma near_sup357_sq_split357 (a b : ℂ) :
    ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    have h1 := norm_add_le b (a - b)
    have h2 : b + (a - b) = a := by ring
    rwa [h2] at h1
  have h3 : ‖a‖ ^ 2 ≤ (‖b‖ + ‖a - b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg a) h 2
  have h4 : (‖b‖ + ‖a - b‖) ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - ‖a - b‖)]
  linarith

/-- Private helper for the assembly: adding the two leaf estimates, the second one
carrying the extra factor 16, gives the combined constant 2 C plus 32 C'. -/
private lemma near_sup357_absorb357 (K C₁ C₂ x y : ℝ)
    (hx : x ≤ C₁ * K) (hy : y ≤ C₂ * (16 * K)) :
    2 * x + 2 * y ≤ (2 * C₁ + 32 * C₂) * K := by
  nlinarith

/-- Assembly of `near_positive_sup357` from the four leaves above: write the value at
phase alpha as the value at phase zero plus the difference, bound the two parts by
steps 1 and 2, use step 4 to replace the scaled phase by 16 and step 3 for the sign of
the weight, and collect 2 C plus 32 C' as the new constant. No step uses
`near_positive_sup357` itself. -/
theorem near_positive_sup357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, Np, hp⟩ := near_sup357_origin357 hG
  obtain ⟨C', hC', Nv, hv⟩ := near_sup357_local_variation357 hG
  refine ⟨2 * C + 32 * C', by linarith, max 1 (max Np Nv), ?_⟩
  intro N hN q hq hqt χ hχ α hα0 hαu
  have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNp : Np < N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNv : Nv < N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hW : (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 :=
    near_sup357_weight_nonneg357 (N := N) (q := q) hN1 hq
  have hLen : 4 * α * (N : ℝ) ≤ 16 :=
    near_sup357_phase_length357 (N := N) (α := α) hN1 hα0 hαu
  have h0 := hp N hNp q hq hqt χ hχ
  have h0' : ‖characterPrime280 χ N 0‖ ^ 2 ≤ C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
    calc ‖characterPrime280 χ N 0‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := h0
      _ = C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by ring
  have hv' := hv N hNv q hq hqt χ hχ α hα0 hαu
  have hvar : ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
      C' * (16 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by
    have hmul : (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) ≤
        16 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
      mul_le_mul_of_nonneg_right hLen hW
    calc ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2
        ≤ C' * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := hv'
      _ = C' * ((4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by ring
      _ ≤ C' * (16 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) :=
          mul_le_mul_of_nonneg_left hmul hC'.le
  have hsplit :=
    near_sup357_sq_split357 (characterPrime280 χ N α) (characterPrime280 χ N 0)
  have hmain : ‖characterPrime280 χ N α‖ ^ 2 ≤
      (2 * C + 32 * C') * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
    le_trans hsplit (near_sup357_absorb357 _ C C' _ _ h0' hvar)
  calc ‖characterPrime280 χ N α‖ ^ 2
      ≤ (2 * C + 32 * C') * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := hmain
    _ = (2 * C + 32 * C') * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by ring

end LeanLab.Linnik1951
