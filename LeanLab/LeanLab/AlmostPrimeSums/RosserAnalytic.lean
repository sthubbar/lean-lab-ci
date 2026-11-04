import LeanLab.AlmostPrimeSums.RosserBounded
import LeanLab.AlmostPrimeSums.RosserCard

/-!
AI wrote this Lean code for CODEX task258. Goldbach is open.
The remaining general K estimates are positive Selberg moments of the
existing Rosser divisor defects. No new sieve axiom or Prop is introduced.
-/

namespace LeanLab.AlmostPrimeSums.Decomp1527b

open Finset Real ArithmeticFunction BoundingSieve

/-- LEAF. Uniform exponential upper defect moment for the existing Rosser
weights for z above the fixed K dependent cutoff. The bounded cutoff
regime is proved in RosserBounded. The finite transform is in RosserDefect.
This is the remaining upper analytic part of IK Lemma 6.3 and Theorem 6.9.
Derived normalized formulation using Heath Brown pp. 31 to 35 and
BJS p. 10 equation 28. The exact cited book pages remain unavailable. -/
theorem rosser_upper_defect_moment_exp (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D true n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. Uniform exponential lower defect moment for the existing Rosser
weights for z above the fixed K dependent cutoff. The bounded cutoff regime
is proved in RosserBounded. The lower defect is nonnegative.
This is the remaining lower analytic part of IK Lemma 6.3 and Theorem 6.9.
Derived normalized formulation using Heath Brown pp. 31 to 35 and
BJS p. 10 equation 28. The exact cited book pages remain unavailable. -/
theorem rosser_lower_defect_moment_exp (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z →
      max 2 (exp (K + 2)) ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      (∑ n ∈ s.prodPrimes.divisors.filter
          (fun n : ℕ => D ≤ (n : ℝ) * z ^ 2 ∧ 9 ≤ n.primeFactors.card),
        s.selbergTerms n * rosserDefect D false n) ≤ C * exp (-(log D / log z)) := by
  sorry

/-- LEAF. Deep. Fundamental lemma of sieve theory, `κ = 1`: given `K ≥ 0` there is `C > 0`
such that whenever all primes of `P` are below `z`, `Ω₁(K)` holds, `z ≥ 2` and `D ≥ z^{10}`,
there are upper and lower bound sieve weights `λ^±` with `|λ^±_d| ≤ 1`, supported on `d ∣ P`,
`d < D`, `λ^±_1 = 1`, `Σ_{d∣n} λ⁺_d ≥ [n=1]` for all `n`,
`Σ_{d∣n} λ⁻_d ≤ [n=1]` for `n ∣ P`, and `|Σ_{d∣P} λ^±_d g(d) − V(z)| ≤ C e^{-s} V(z)`, `s = log D/log z`.
Iwaniec-Kowalski Lemma 6.3 and Theorem 6.9 (`D ≥ z^{9κ+1}`).
Unit U-1527. -/
theorem fundamental_lemma (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : BoundingSieve) (z D : ℝ), 2 ≤ z → z ^ 10 ≤ D →
      (∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) → LinearDensity s K →
      ∃ lp lm : ℕ → ℝ,
        (∀ d, |lp d| ≤ 1 ∧ |lm d| ≤ 1) ∧ lp 1 = 1 ∧ lm 1 = 1 ∧
        (∀ d, lp d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        (∀ d, lm d ≠ 0 → d ∣ s.prodPrimes ∧ (d : ℝ) < D) ∧
        IsUpperMoebius lp ∧
        (∀ n : ℕ, n ∣ s.prodPrimes → ∑ d ∈ n.divisors, lm d ≤ if n = 1 then 1 else 0) ∧
        |s.mainSum lp - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) ∧
        |s.mainSum lm - ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
          C * exp (-(log D / log z)) * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
  obtain ⟨Cp, hCp, hupper⟩ := rosser_upper_defect_moment_exp K hK
  obtain ⟨Cm, hCm, hlower⟩ := rosser_lower_defect_moment_exp K hK
  let B := max 2 (exp (K + 2))
  obtain ⟨Cb, hCb, hbounded⟩ := rosser_defect_moment_exp_bounded K B hK (le_max_left _ _)
  refine ⟨Cb + Cp + Cm, add_pos (add_pos hCb hCp) hCm, ?_⟩
  intro s z D hz hD hP hden
  have hzD : z ≤ D := by
    calc
      z = z ^ 1 := by simp
      _ ≤ z ^ 10 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ ≤ D := hD
  have hD1 : 1 < D := by linarith
  obtain ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, hmp, hmm⟩ :=
    rosser_fundamental_weights s z D hzD hD1 hP
  have hV : 0 ≤ ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) :=
    Finset.prod_nonneg fun p hp =>
      (sub_pos.mpr (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))).le
  have herror : ∀ upper : Bool,
      |s.mainSum (rosserWeight D upper) -
        (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p))| ≤
        (Cb + Cp + Cm) * exp (-(log D / log z)) *
          ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) := by
    intro upper
    have hm : (∑ n ∈ s.prodPrimes.divisors,
        s.selbergTerms n * rosserDefect D upper n) ≤
          (Cb + Cp + Cm) * exp (-(log D / log z)) := by
      by_cases hzB : z ≤ B
      · exact (hbounded s z D hz hzB hD hP hden upper).trans
          (mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le)
      · have hlarge : B ≤ z := (lt_of_not_ge hzB).le
        rw [rosser_defect_moment_eq_tail_many_primes s D z hz hD hP]
        cases upper
        · exact (hlower s z D hz hlarge hD hP hden).trans
            (mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le)
        · exact (hupper s z D hz hlarge hD hP hden).trans
            (mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le)
    rw [rosser_mainSum_error_eq]
    exact (mul_le_mul_of_nonneg_left hm hV).trans_eq (by ring)
  refine ⟨lp, lm, hb, hp1, hm1, hsp, hsm, hu, hl, ?_, ?_⟩
  · simpa only [hmp] using herror true
  · simpa only [hmm] using herror false

end LeanLab.AlmostPrimeSums.Decomp1527b
