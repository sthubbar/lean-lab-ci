/-
Split of the local variation bound `near_sup357_local_variation357` into three
smaller steps. Nothing here changes the statement: the assembly
`near_sup357_local_variation357_split` below states it character for character and
proves it from the three OPEN leaves, which record, in order, (1) the identity that
writes the change of the damped character prime sum between phase zero and phase
alpha as the integral of its derivative in the phase, (2) the plain
Cauchy-Schwarz inequality for an interval integral of a complex valued function, and
(3) the mean square estimate for that derivative over the permitted phase range.
The proof of the assembly does not use `near_sup357_local_variation357`.
-/
import LeanLab.Linnik1951.SPLIT_near_positive_sup357

namespace LeanLab.Linnik1951

/-- LEAF: Step 1 of 3: the change of the damped character prime sum over the phase is
the integral of its derivative. The derivative in the phase of the exponential factor
of the summand at prime p carries the factor minus two pi p, so the differentiated
series is the one displayed. This is an identity in the complex numbers and it uses
no estimate at all: the two sides are equal for every nonnegative phase, and both
sides vanish at phase zero. -/
theorem near_sup357_difference_integral357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (α : ℝ) (hα : 0 ≤ α) :
    characterPrime280 χ N α - characterPrime280 χ N 0 =
      ∫ β in (0 : ℝ)..α, ∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) := by
  sorry

/-- LEAF: Step 2 of 3: the Cauchy-Schwarz inequality for an interval integral. For
any complex valued function on the line and any nonnegative length alpha, the square
of the norm of the integral from zero to alpha is at most alpha times the integral of
the squared norm. The content is that an integral over a short interval cannot be
large unless the squared norm is large somewhere on it; no arithmetic information
enters, and at alpha equal to zero both sides are zero. -/
theorem near_sup357_integral_norm_sq357 (g : ℝ → ℂ) {α : ℝ} (hα : 0 ≤ α) :
    ‖∫ β in (0 : ℝ)..α, g β‖ ^ 2 ≤ α * ∫ β in (0 : ℝ)..α, ‖g β‖ ^ 2 := by
  sorry

/-- LEAF: Step 3 of 3: the mean square estimate for the derivative of the damped
character prime sum over the permitted phase range. There is a fixed positive constant
C such that for large N, every modulus q up to N to the one seventh, every nonprincipal
character mod q and every phase alpha between zero and 4 over N, the integral over the
phase interval from zero to alpha of the squared norm of the differentiated series is
at most C times alpha times N squared times N over q times log N to the fifth. The
factor N squared is the size of the differentiation, and at alpha equal to zero the
claim reads zero at most zero. -/
theorem near_sup357_derivative_moment357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            (∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2) ≤
              C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  sorry

/-- Assembly of `near_sup357_local_variation357` from the three leaves above: write
the change of the sum as the integral of its derivative, apply Cauchy-Schwarz to that
integral, bound the resulting mean square by step 3, and use the fact that the scaled
phase alpha times N is at most 4 to turn the square of the scaled phase back into the
first power that the statement asks for. The weight N over q times log N to the fifth
is nonnegative, which is where its sign is used. No step uses
`near_sup357_local_variation357` itself. -/
theorem near_sup357_local_variation357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
              C * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  obtain ⟨C, hC, Nd, hder⟩ := near_sup357_derivative_moment357 hG
  refine ⟨C, hC, max 1 Nd, ?_⟩
  intro N hN q hq hqt χ hχ α hα0 hαu
  have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNd : Nd < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hW : (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 :=
    near_sup357_weight_nonneg357 (N := N) (q := q) hN1 hq
  have hid := near_sup357_difference_integral357 (χ := χ) (N := N) (α := α) hα0
  have hcs := near_sup357_integral_norm_sq357
    (g := fun β : ℝ => ∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) hα0
  have hmom := hder N hNd q hq hqt χ hχ α hα0 hαu
  have hstep : ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
      α * ∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2 := by
    rw [hid]
    exact hcs
  have hαN4 : α * (N : ℝ) ≤ 4 := by
    have h1 : α * (N : ℝ) ≤ (4 / (N : ℝ)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hαu hNpos.le
    have h2 : (4 / (N : ℝ)) * (N : ℝ) = 4 := by
      rw [div_mul_cancel₀ _ (ne_of_gt hNpos)]
    linarith
  have hαN0 : (0 : ℝ) ≤ α * (N : ℝ) := mul_nonneg hα0 hNpos.le
  have hsq : (α * (N : ℝ)) ^ 2 ≤ 4 * (α * (N : ℝ)) := by
    nlinarith [hαN4, hαN0]
  calc ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2
      ≤ α * ∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2 := hstep
    _ ≤ α * (C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) :=
        mul_le_mul_of_nonneg_left hmom hα0
    _ = C * ((α * (N : ℝ)) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by ring
    _ ≤ C * ((4 * (α * (N : ℝ))) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        exact mul_le_mul_of_nonneg_right hsq hW
    _ = C * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by ring

end LeanLab.Linnik1951
