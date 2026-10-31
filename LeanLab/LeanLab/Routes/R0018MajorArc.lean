/-
Route R-0018, T3, part 2: the major arc constant of the discrete circle method at denominator N.

The frequencies a/N have reduced denominators q ∣ N only; the classical major arc heuristic
S(b/q) ≈ μ(q)/φ(q) · π(N) then gives Σ_{q ∣ N} μ(q)²/φ(q) · π(N)²/N, and
`sum_sq_moebius_div_totient` proves Σ_{q ∣ n} μ(q)²/φ(q) = n/φ(n) for every n ≥ 1.
For N = 2^(k+1) this is 2, while the Hardy-Littlewood constant is 2 C₂ with C₂ ≤ 0.66017
by the lab's ChenExplicit.TwinCUpper; so the small denominator arcs overshoot r(N) by a
factor at least 2/1.32034, and the remaining arcs must carry a negative main term.

AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace LeanLab.Routes.R0018

/-- `q ↦ μ(q)² / φ(q)` as a rational arithmetic function. -/
noncomputable def sqMuDivPhi : ArithmeticFunction ℚ :=
  ⟨fun d => ((μ d : ℤ) : ℚ) ^ 2 / (Nat.totient d : ℚ), by simp⟩

/-- `n ↦ n / φ(n)` as a rational arithmetic function. -/
noncomputable def nDivPhi : ArithmeticFunction ℚ :=
  ⟨fun n => (n : ℚ) / (Nat.totient n : ℚ), by simp⟩

lemma sqMuDivPhi_apply (d : ℕ) : sqMuDivPhi d = ((μ d : ℤ) : ℚ) ^ 2 / (Nat.totient d : ℚ) := rfl
lemma nDivPhi_apply (n : ℕ) : nDivPhi n = (n : ℚ) / (Nat.totient n : ℚ) := rfl

lemma isMult_sqMuDivPhi : sqMuDivPhi.IsMultiplicative := by
  refine ⟨by simp [sqMuDivPhi_apply], fun {m n} hmn => ?_⟩
  simp only [sqMuDivPhi_apply]
  rw [isMultiplicative_moebius.map_mul_of_coprime hmn, Nat.totient_mul hmn]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

lemma isMult_nDivPhi : nDivPhi.IsMultiplicative := by
  refine ⟨by simp [nDivPhi_apply], fun {m n} hmn => ?_⟩
  simp only [nDivPhi_apply]
  rw [Nat.totient_mul hmn]
  push_cast
  rw [mul_div_mul_comm]

/-- **Σ_{q ∣ n} μ(q)²/φ(q) = n/φ(n)** for every `n ≥ 1`. -/
theorem sum_sq_moebius_div_totient {n : ℕ} (hn : n ≠ 0) :
    ∑ q ∈ n.divisors, ((μ q : ℤ) : ℚ) ^ 2 / (Nat.totient q : ℚ) =
      (n : ℚ) / (Nat.totient n : ℚ) := by
  have hF : (sqMuDivPhi * (ζ : ArithmeticFunction ℚ)).IsMultiplicative :=
    isMult_sqMuDivPhi.mul isMultiplicative_zeta.natCast
  have key : sqMuDivPhi * (ζ : ArithmeticFunction ℚ) = nDivPhi := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hF _ isMult_nDivPhi]
    intro p k hp
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, nDivPhi_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [sqMuDivPhi_apply]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Finset.sum_range_succ']
      have hrest : ∀ i ∈ range j, sqMuDivPhi (p ^ (i + 1 + 1)) = 0 := by
        intro i _
        rw [sqMuDivPhi_apply, moebius_apply_prime_pow hp (by omega)]
        simp
      rw [Finset.sum_range_succ', Finset.sum_eq_zero hrest]
      rw [sqMuDivPhi_apply, sqMuDivPhi_apply, moebius_apply_prime_pow hp (by omega)]
      simp only [zero_add, pow_one, pow_zero, ite_true, Nat.totient_one]
      rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime hp]
      have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
      have hp0 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
        rw [Nat.cast_sub hp.one_le]; simp
      push_cast [hp0]
      field_simp
      simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_pow, mul_one]
      ring
  have := congrArg (fun f : ArithmeticFunction ℚ => f n) key
  simp only [coe_mul_zeta_apply] at this
  simpa [sqMuDivPhi_apply, nDivPhi_apply] using this

/-- For `N = 2^(k+1)` the major arc constant `N/φ(N)` is exactly 2. -/
theorem major_const_two_pow (k : ℕ) :
    ∑ q ∈ (2 ^ (k + 1)).divisors, ((μ q : ℤ) : ℚ) ^ 2 / (Nat.totient q : ℚ) = 2 := by
  rw [sum_sq_moebius_div_totient (by positivity), Nat.totient_prime_pow_succ Nat.prime_two]
  have : (2 : ℚ) ^ k ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Vacuity and a second check: `n = 30`, `30/φ(30) = 30/8`. -/
example : ∑ q ∈ (30 : ℕ).divisors, ((μ q : ℤ) : ℚ) ^ 2 / (Nat.totient q : ℚ) = 30 / 8 := by
  rw [sum_sq_moebius_div_totient (by norm_num)]
  rw [show Nat.totient 30 = 8 by decide]; norm_num

end LeanLab.Routes.R0018

#print axioms LeanLab.Routes.R0018.sum_sq_moebius_div_totient
#print axioms LeanLab.Routes.R0018.major_const_two_pow
