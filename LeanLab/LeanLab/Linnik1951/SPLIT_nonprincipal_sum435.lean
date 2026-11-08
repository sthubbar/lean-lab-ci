/-
Split of the nonprincipal mean square estimate for the damped prime character
sums into three smaller supplies: the single character mean square estimate of
Section 5 at a radius at most two, the count of nonprincipal characters against
the totient, and the transfer from a per character bound to the summed form.
The assembly below proves the exact statement of nonprincipal_sum435 from those
supplies without using it.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. First step of the estimate, the single character mean square bound.
Under the vanishing hypothesis, for one nonprincipal character of a modulus q at
least two with q at most N to the one seventh, the square integral of the damped
character prime sum over an interval of radius r is at most a constant times N
times the thirteenth power of log N times r, for every positive radius r of at
most two. One character only: there is no sum over characters and no totient
factor here. -/
theorem character_mean_square435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ r : ℝ, 0 < r → r ≤ 2 →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ z in -r..r, ‖characterPrime280 χ N z‖ ^ 2) ≤
            B * (N : ℝ) * Real.log N ^ 13 * r := by
  sorry

/-- LEAF. Second step of the estimate, the counting step. The nonprincipal
characters of a modulus q at least two are at most totient q in number: the
whole character group has totient q elements and one of them is principal. -/
theorem nonprincipal_card435 (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card ≤ q.totient := by
  sorry

/-- LEAF. Third step of the estimate, the summation step. A sum of real terms
indexed by the nonprincipal characters of a modulus q at least two, each term at
most a nonnegative M, is at most totient q times M. -/
theorem nonprincipal_sum_le435 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (M : ℝ) (hM : 0 ≤ M)
    (f : DirichletCharacter ℂ q → ℝ) (hf : ∀ χ, χ ≠ 1 → f χ ≤ M) :
    (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), f χ) ≤
      (q.totient : ℝ) * M := by
  sorry

/-- The nonprincipal mean square estimate. The exact statement of
nonprincipal_sum435, proved from the three supplies above without using it: the
single character bound at radius two over R, the character count, and the
summation step combined by real arithmetic. -/
theorem nonprincipal_sum435_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ X : ℝ, 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
          X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by
  classical
  obtain ⟨B, hB, N0, hN0⟩ := character_mean_square435 hG
  refine ⟨2 * B, by positivity, max N0 1, ?_⟩
  intro N hN q _ hq hqt R hR hRle
  have hN0lt : N0 < N := lt_of_le_of_lt (le_max_left N0 1) hN
  have hN1 : 1 ≤ N := by
    have h := le_max_right N0 1
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hrpos : (0 : ℝ) < 2 / R := by positivity
  have hr2 : 2 / R ≤ 2 := by
    rw [div_le_iff₀ hRpos]
    linarith
  have hMnn : (0 : ℝ) ≤ B * (N : ℝ) * Real.log N ^ 13 * (2 / R) :=
    mul_nonneg (mul_nonneg (mul_nonneg hB.le hNpos.le) (pow_nonneg hlog 13)) hrpos.le
  have hpt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
        B * (N : ℝ) * Real.log N ^ 13 * (2 / R) := by
    intro χ hχ
    exact hN0 N hN0lt q hq hqt (2 / R) hrpos hr2 χ hχ
  have key : (q.totient : ℝ) * (B * (N : ℝ) * Real.log N ^ 13 * (2 / R)) =
      2 * B * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by
    field_simp
  refine le_trans (nonprincipal_sum_le435 q hq (B * (N : ℝ) * Real.log N ^ 13 * (2 / R))
    hMnn (fun χ => ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) hpt) ?_
  exact le_of_eq key

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.nonprincipal_sum435_split
