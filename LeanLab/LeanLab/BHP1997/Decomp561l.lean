/-
P0069 page 3 and page 9 display 2.13, finite odd modulus diagnostics.
These do not establish the full asymptotic hypotheses or refute the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561j
import Mathlib.NumberTheory.DirichletCharacter.Bounds
namespace LeanLab.BHP1997.Decomp561l
open Classical Complex AddCircle Finset Decomp561j

/-- P0069 page 3 hypotheses iii and iv and page 9 display 2.13.
Auxiliary finite nonunit diagnostic. For odd modulus q, an even supported phase
of denominator 4L times a character changes sign after 2qL indices.
This is not the full asymptotic counterexample. -/
theorem odd_character_antiperiod561 (L q : ℕ) (hL : 0 < L) (hq : Odd q)
    (χ : DirichletCharacter ℂ q) :
    Function.Antiperiodic
      (fun m : ℕ => evenPhaseCoeff561 (1 / (4 * (L : ℝ))) m * χ (m : ZMod q))
      (2 * q * L) := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hz : @fourier 1 ((2 * q * L : ℕ) : ℤ)
      ((1 / (4 * (L : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = -1 := by
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one]
    have he : 2 * Real.pi * Complex.I * (((2 * q * L : ℕ) : ℤ) : ℂ) *
        ((1 / (4 * (L : ℝ)) : ℝ) : ℂ) / 1 =
        (q : ℂ) * (Real.pi * Complex.I) := by
      push_cast
      field_simp [hL']; ring
    rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I, hq.neg_one_pow]
  intro m
  dsimp only
  have hd : Even (2 * q * L) := ⟨q * L, by ring⟩
  have he : Even (m + 2 * q * L) ↔ Even m := by simp [Nat.even_add, hd]
  have hc : χ ((m + 2 * q * L : ℕ) : ZMod q) = χ (m : ZMod q) := by
    simp [Nat.cast_add, Nat.cast_mul]
  rw [hc]
  unfold evenPhaseCoeff561
  by_cases hm : Even m
  · simp only [he, hm, ite_true]
    rw [Nat.cast_add, fourier_add, hz]
    ring
  · simp [he, hm]
/-- P0069 page 3 hypotheses iii and iv, auxiliary finite cancellation estimate.
An antiperiodic complex sequence bounded by one has every interval prefix
bounded by twice the antiperiod. This supplies a finite diagnostic, not a
uniform asymptotic character hypothesis. -/
theorem antiperiodic_prefix_norm561 (f : ℕ → ℂ) (d : ℕ) (hd : 0 < d)
    (hf : Function.Antiperiodic f d) (hb : ∀ m, ‖f m‖ ≤ 1) (a N : ℕ) :
    ‖∑ i ∈ Finset.range N, f (a + i)‖ ≤ (2 * d : ℕ) := by
  have hp := hf.periodic_two_mul
  induction N using Nat.strong_induction_on generalizing a with
  | h N ih =>
    by_cases hN : N < 2 * d
    · calc
        _ ≤ ∑ i ∈ Finset.range N, ‖f (a + i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hb _)
        _ = (N : ℝ) := by simp
        _ ≤ (2 * d : ℕ) := by exact_mod_cast hN.le
    · have hN' : 2 * d ≤ N := by omega
      have hz : (∑ i ∈ Finset.range (2 * d), f (a + i)) = 0 := by
        rw [show 2 * d = d + d by omega, Finset.sum_range_add]
        have hs : (∑ i ∈ Finset.range d, f (a + (d + i))) =
            -(∑ i ∈ Finset.range d, f (a + i)) := by
          calc
            _ = ∑ i ∈ Finset.range d, -f (a + i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [show a + (d + i) = (a + i) + d by omega, hf]
            _ = _ := by rw [Finset.sum_neg_distrib]
        rw [hs]
        ring
      have ht : (∑ i ∈ Finset.range (N - 2 * d), f (a + (2 * d + i))) =
          ∑ i ∈ Finset.range (N - 2 * d), f (a + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show a + (2 * d + i) = (a + i) + 2 * d by omega, hp]
      have he : N = 2 * d + (N - 2 * d) := by omega
      rw [he, Finset.sum_range_add, hz, zero_add, ht]
      exact ih (N - 2 * d) (by omega) a

/-- P0069 page 3 hypotheses iii and iv and page 9 display 2.13.
Auxiliary finite odd modulus cancellation. Every interval prefix of the even
supported phase of denominator 4L times a character modulo odd q has norm at
most 4qL. This is the uniform finite bound, not the complete asymptotic family
or the asserted minor arc counterexample. -/
theorem odd_character_prefix_bound561 (L q : ℕ) (hL : 0 < L) (hq : Odd q)
    (χ : DirichletCharacter ℂ q) (a N : ℕ) :
    ‖∑ i ∈ Finset.range N,
      evenPhaseCoeff561 (1 / (4 * (L : ℝ))) (a + i) * χ ((a + i : ℕ) : ZMod q)‖ ≤
      (4 * q * L : ℕ) := by
  have hq0 : 0 < q := by obtain ⟨k, hk⟩ := hq; omega
  have hb (m : ℕ) :
      ‖evenPhaseCoeff561 (1 / (4 * (L : ℝ))) m * χ (m : ZMod q)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (evenPhaseCoeff_norm_le561 _ m) (χ.norm_le_one _) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have h := antiperiodic_prefix_norm561
    (fun m : ℕ => evenPhaseCoeff561 (1 / (4 * (L : ℝ))) m * χ (m : ZMod q))
    (2 * q * L) (by positivity) (odd_character_antiperiod561 L q hL hq χ) hb a N
  have he : 2 * (2 * q * L) = 4 * q * L := by ring
  simpa only [he] using h

end LeanLab.BHP1997.Decomp561l
