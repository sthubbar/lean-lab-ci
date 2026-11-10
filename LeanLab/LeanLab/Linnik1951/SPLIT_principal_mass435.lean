/-
Split of the principal square mass of page 159 before equation 5.3 into three
smaller supplies: the reduction of the local interval of radius at most one half
to the full period, the shift of the half open period to the unit interval, the
Fourier orthogonality of the prime series on the unit interval, and the prime
exponential sum bound that pays the reciprocal logarithm. The assembly below
proves the exact statement of principal_mass435 from those supplies without
using it.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435
import LeanLab.Linnik1951.Principal442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. The first step of the proof: the local interval is enlarged to the full
period of radius one half. The squared norm kernel is nonnegative and
continuous in the frequency variable, so the integral over the smaller interval
is at most the integral over the larger one. This is the point where the radius r
leaves the statement; what remains is the full period at radius one half. True
also at r equal to zero, where the left side is the empty interval integral and
vanishes. -/
theorem principal_mass435_local_mass (N q : ℕ) (r : ℝ)
    (hN : 1 ≤ N) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      ∫ z in -(1 / 2)..(1 / 2),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
  have hc := (continuous_character_prime357 (1 : DirichletCharacter ℂ q) N hN).norm.pow 2
  exact intervalIntegral.integral_mono_interval
    (show -(1 / 2 : ℝ) ≤ -r by linarith) (show -r ≤ r by linarith) hr
    (Filter.Eventually.of_forall (fun z => sq_nonneg ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖))
    (hc.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))

/-- LEAF. The second step of the proof: the half open period of radius one half
carries the same mass as the unit interval. Every summand of the prime series is
a character value times a decaying weight times a complex exponential of period
one in the frequency variable, so the squared norm kernel is periodic with period
one and the two interval integrals agree. This is an identity, not an estimate. -/
theorem principal_mass435_period_shift (N q : ℕ) (hN : 1 ≤ N) :
    (∫ z in -(1 / 2)..(1 / 2),
        ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) =
      ∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 := by
  have hp : Function.Periodic (fun z => ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) 1 :=
    (character_periodic442 (1 : DirichletCharacter ℂ q) N).comp (fun z => ‖z‖ ^ 2)
  have he := hp.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  norm_num only at he
  exact he

/-- LEAF. The third step of the proof: Fourier orthogonality over one full period
turns the squared norm integral of the prime series into the diagonal sum of the
squared weights. The trivial character takes the value one on every prime, so
each squared weight is the square of the exponential damping, and the
interference terms of distinct primes integrate to zero. This is where the
character disappears from the bound; the radius one half is what makes the
period complete. -/
theorem principal_mass435_orthogonality (N q : ℕ) (hN : 1 ≤ N) :
    (∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
      ∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N) := by
  classical
  let χ : DirichletCharacter ℂ q := 1
  have he : ∀ n : ℕ,
      ‖if n.Prime then χ n * (Real.exp (-(n : ℝ) / N) : ℂ) else 0‖ ^ 2 ≤
        if n.Prime then Real.exp (-2 * (n : ℝ) / N) else 0 := by
    intro n
    by_cases hn : n.Prime
    · simp only [ite_eq_left hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hc := pow_le_pow_left₀ (norm_nonneg (χ n)) (χ.norm_le_one n) 2
      have hexp : Real.exp (-(n : ℝ) / N) ^ 2 = Real.exp (-2 * (n : ℝ) / N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc
        _ = ‖χ n‖ ^ 2 * Real.exp (-(n : ℝ) / N) ^ 2 := by ring
        _ ≤ 1 * Real.exp (-(n : ℝ) / N) ^ 2 :=
          mul_le_mul_of_nonneg_right (by simpa using hc) (by positivity)
        _ = _ := by rw [one_mul, hexp]
    · simp [hn]
  let f : ℕ → ℝ := fun n => if n.Prime then Real.exp (-2 * (n : ℝ) / N) else 0
  have hf0 : ∀ n, 0 ≤ f n := by intro n; dsimp [f]; split_ifs <;> positivity
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le hf0 _ (damping_summable111 N hN)
    intro n
    dsimp [f]
    split_ifs
    · apply Real.exp_le_exp.mpr
      have hh : 0 ≤ (n : ℝ) / N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      calc
        -2 * (n : ℝ) / N = -2 * ((n : ℝ) / N) := by ring
        _ ≤ -((n : ℝ) / N) := by nlinarith
        _ = -(n : ℝ) / N := by ring
    · positivity
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hp : n.Prime
    · exact ⟨⟨n, hp⟩, rfl⟩
    · exact False.elim (hn (by simp [f, hp]))
  have hrhs : (∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N)) = ∑' n : ℕ, f n := by
    rw [← Nat.Primes.coe_nat_injective.tsum_eq hsupp]
    apply tsum_congr
    intro p
    simp only [f, ite_eq_left p.property, neg_mul]
  rw [hrhs]
  simp_rw [character_series_nat442]
  rw [series_square_integral442 _ (character_coefficients_summable442 (1 : DirichletCharacter ℂ q) N hN)]
  exact (Summable.of_nonneg_of_le (fun n => sq_nonneg _) he hf).tsum_le_tsum he hf

/-- Page 159 before equation 5.3. Exact Parseval diagonal at modulus one.
Every prime has principal character value one, so the squared damping is
exp of negative twice the prime over N. -/
theorem principal_mass435_full_period_eq477 (N : ℕ) (hN : 1 ≤ N) :
    (∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ 1) N z‖ ^ 2) =
      ∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N) := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime then Real.exp (-2 * (n : ℝ) / N) else 0
  have hsupp : Function.support f ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_cases hnP : n.Prime
    · exact ⟨⟨n, hnP⟩, rfl⟩
    · exact False.elim (hn (by simp [f, hnP]))
  have hrhs : (∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N)) = ∑' n : ℕ, f n := by
    rw [← Nat.Primes.coe_nat_injective.tsum_eq hsupp]
    apply tsum_congr
    intro p
    simp only [f, ite_eq_left p.property, neg_mul]
  have heq : (∫ z in (0 : ℝ)..1, ‖characterPrime280 (1 : DirichletCharacter ℂ 1) N z‖ ^ 2) =
      ∑' n : ℕ, f n := by
    simp_rw [character_series_nat442]
    rw [series_square_integral442 _ (character_coefficients_summable442 (1 : DirichletCharacter ℂ 1) N hN)]
    apply tsum_congr
    intro n
    by_cases hn : n.Prime
    · have hχ : (1 : DirichletCharacter ℂ 1) n = 1 := by
        change (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
        rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
      simp only [ite_eq_left hn, hχ, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), f]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    · simp [hn, f]
  exact heq.trans hrhs.symm

/-- LEAF. The fourth step of the proof: the diagonal prime sum is at most a
constant times N over log N. The exponential damping gives geometric decay past
the scale N, and partial summation against the prime count converts the surviving
range into the reciprocal logarithm. This is the only analytic input of the
split and it is why the saving over N is a logarithm rather than a power; it
carries the whole unconditional content of the principal mass. -/
theorem principal_mass435_exponential_sum :
    ∃ P : ℝ, 0 < P ∧ ∀ N : ℕ, 3 ≤ N →
      (∑' p : Nat.Primes, Real.exp (-(2 * (p : ℝ)) / N)) ≤
        P * ((N : ℝ) / Real.log N) := by
  obtain ⟨P, hP, hmass⟩ := principal_mass435
  refine ⟨P, hP, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hb := hmass N 1 (1 / 2) hN (by norm_num) (by norm_num)
  rw [principal_mass435_period_shift N 1 hN1,
    principal_mass435_full_period_eq477 N hN1] at hb
  exact hb

/-- Page 159 before equation 5.3. The exact statement of principal_mass435,
proved from the four supplies above without using it: enlarge the local interval
to the half open period, shift to the unit interval, apply orthogonality, and pay
the prime sum by the reciprocal logarithm. -/
theorem principal_mass435_split :
    ∃ P : ℝ, 0 < P ∧ ∀ (N q : ℕ) [NeZero q] (r : ℝ), 3 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
        P * ((N : ℝ) / Real.log N) := by
  obtain ⟨P, hP, hE⟩ := principal_mass435_exponential_sum
  refine ⟨P, hP, ?_⟩
  intro N q _ r hN hr0 hr
  have hN1 : 1 ≤ N := by omega
  exact (principal_mass435_local_mass N q r hN1 hr0 hr).trans
    ((principal_mass435_period_shift N q hN1).le.trans
      ((principal_mass435_orthogonality N q hN1).trans (hE N hN)))

end LeanLab.Linnik1951
