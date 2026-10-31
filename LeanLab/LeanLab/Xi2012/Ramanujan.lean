import LeanLab.Xi2012.PrimePowerComparison
import LeanLab.PNTPort.Vinogradov.SingPos

/-!
Xi 2012, arXiv 1206.2148v1, page 4 Lemma 2.
The finite exponential sum uses natural reduced residue classes.
The existing PNTPort bridge identifies it with the divisor formula.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset

/-- Page 4: the Ramanujan sum over reduced natural residues modulo q. -/
noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (range q).filter (fun a : ℕ => Nat.Coprime a q),
    fourierPhase ((n : ℝ) / q) a

/-- Identify the exponential definition with the lab's arithmetic divisor formula. -/
theorem ramanujanSum_eq_arithmetic {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ramanujanSum q n = (LeanLab.HeathBrown1985.ramanujan q n : ℂ) := by
  unfold ramanujanSum
  calc
    (∑ a ∈ (range q).filter (fun a : ℕ => Nat.Coprime a q),
        fourierPhase ((n : ℝ) / q) a) =
      ∑ a ∈ (range q).filter (fun a : ℕ => Nat.Coprime a q),
        LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * a / q) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold fourierPhase LeanLab.PNTPort.LargeSieve.e
      congr 1
      push_cast
      ring
    _ = _ := LeanLab.PNTPort.Vinogradov.ramanujan_sum hq n

/-- Page 4 Lemma 2 part 2, with divisibility equivalent to the printed coprimality case. -/
theorem ramanujanSum_prime {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    ramanujanSum p n = if p ∣ n then (p : ℂ) - 1 else -1 := by
  rw [ramanujanSum_eq_arithmetic hp.one_lt.le n,
    LeanLab.PNTPort.Vinogradov.ramanujan_prime hp n]
  by_cases h : p ∣ n <;> simp [h]

/-- Page 4 Lemma 2 part 1, multiplicativity in the positive modulus. -/
theorem ramanujanSum_mul {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hcop : Nat.Coprime r s) (n : ℕ) :
    ramanujanSum (r * s) n = ramanujanSum r n * ramanujanSum s n := by
  have hrs : 1 ≤ r * s := by simpa using Nat.mul_le_mul hr hs
  have h := (LeanLab.PNTPort.Vinogradov.cR_mult n).map_mul_of_coprime hcop
  rw [LeanLab.PNTPort.Vinogradov.cR_apply hrs n,
    LeanLab.PNTPort.Vinogradov.cR_apply hr n,
    LeanLab.PNTPort.Vinogradov.cR_apply hs n] at h
  rw [ramanujanSum_eq_arithmetic hrs n, ramanujanSum_eq_arithmetic hr n,
    ramanujanSum_eq_arithmetic hs n]
  exact_mod_cast h

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open LeanLab.PNTPort.Vinogradov (cR cR_mult cR_apply gDiv gDiv_apply)

/-- Moebius inversion for the arithmetic Ramanujan function. -/
theorem cR_mul_zeta (n : ℕ) : cR n * (ζ : ArithmeticFunction ℝ) = gDiv n := by
  unfold cR
  rw [mul_assoc, coe_moebius_mul_coe_zeta, mul_one]

/-- On successive prime powers, Moebius inversion is a difference. -/
theorem cR_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (n k : ℕ) :
    cR n (p ^ (k + 1)) = gDiv n (p ^ (k + 1)) - gDiv n (p ^ k) := by
  have htop := congrArg (fun f : ArithmeticFunction ℝ => f (p ^ (k + 1))) (cR_mul_zeta n)
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at htop
  have hprev := congrArg (fun f : ArithmeticFunction ℝ => f (p ^ k)) (cR_mul_zeta n)
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp] at hprev
  linarith

/-- The prime-power case of the gcd bound in page 4 Lemma 2. -/
theorem abs_cR_prime_pow_le_gcd {p : ℕ} (hp : Nat.Prime p) (n k : ℕ) :
    |cR n (p ^ (k + 1))| ≤ (Nat.gcd n (p ^ (k + 1)) : ℝ) := by
  have hdiv : p ^ k ∣ p ^ (k + 1) := by
    use p
    rw [pow_succ]
  rw [cR_prime_pow_succ hp n k]
  by_cases htop : p ^ (k + 1) ∣ n
  · have hprev := hdiv.trans htop
    simp only [gDiv_apply, ite_eq_left htop, ite_eq_left hprev, Nat.gcd_eq_right htop]
    have hpow : ((p ^ k : ℕ) : ℝ) ≤ ((p ^ (k + 1) : ℕ) : ℝ) := by
      rw [pow_succ, Nat.cast_mul]
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast hp.one_lt.le)
    rw [abs_of_nonneg (sub_nonneg.mpr hpow)]
    exact sub_le_self _ (Nat.cast_nonneg _)
  · by_cases hprev : p ^ k ∣ n
    · simp only [gDiv_apply, ite_eq_right htop, ite_eq_left hprev, zero_sub, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (p ^ k) : (0 : ℝ) ≤ (p ^ k : ℕ))]
      exact_mod_cast Nat.le_of_dvd
        (Nat.gcd_pos_of_pos_right n (pow_pos hp.pos (k + 1))) (Nat.dvd_gcd hprev hdiv)
    · simp only [gDiv_apply, ite_eq_right htop, ite_eq_right hprev, sub_self, abs_zero]
      exact Nat.cast_nonneg _

/-- The arithmetic Ramanujan gcd bound for every natural modulus. -/
theorem abs_cR_le_gcd (n q : ℕ) : |cR n q| ≤ (Nat.gcd n q : ℝ) := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero =>
    simpa only [ArithmeticFunction.map_zero, abs_zero, Nat.gcd_zero_right] using
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  | one =>
    rw [(cR_mult n).1]
    simp
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k => simpa using abs_cR_prime_pow_le_gcd hp n k
  | coprime a b _ha _hb hab ihA ihB =>
    rw [(cR_mult n).map_mul_of_coprime hab, abs_mul, Nat.Coprime.gcd_mul n hab,
      Nat.cast_mul]
    exact mul_le_mul ihA ihB (abs_nonneg _) (Nat.cast_nonneg _)

/-- Page 4 Lemma 2 part 1, the full gcd bound for the exponential sum. -/
theorem norm_ramanujanSum_le_gcd {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ‖ramanujanSum q n‖ ≤ (Nat.gcd n q : ℝ) := by
  rw [ramanujanSum_eq_arithmetic hq n, Complex.norm_real, Real.norm_eq_abs,
    ← cR_apply hq n]
  exact abs_cR_le_gcd n q

end LeanLab.Xi2012.NatEncoding
