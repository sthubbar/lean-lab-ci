import Mathlib

/-!
The finite convolution behind page 50 equation 3.5.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- Divide each coefficient of an arithmetic function by its index. -/
def divideByN (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n / n, by simp⟩

lemma divideByN_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideByN f n = f n / n := rfl

lemma divideByN_mul (f h : ArithmeticFunction ℝ) :
    divideByN (f * h) = divideByN f * divideByN h := by
  ext n
  simp only [divideByN_apply, mul_apply, sum_div]
  apply sum_congr rfl
  intro d hd
  rw [div_mul_div_comm, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hd).1]

lemma divideByN_one : divideByN (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1
  · subst n; simp [divideByN_apply]
  · simp [divideByN_apply, one_apply, hn]

/-- The coefficients of zeta at w + 1. -/
def reciprocal : ArithmeticFunction ℝ := divideByN (ζ : ArithmeticFunction ℝ)

/-- The reciprocal coefficients of zeta at w + 1. -/
def inverseReciprocal : ArithmeticFunction ℝ := divideByN (μ : ArithmeticFunction ℝ)

lemma inverse_reciprocal : inverseReciprocal * reciprocal = 1 := by
  rw [inverseReciprocal, reciprocal, ← divideByN_mul,
    coe_moebius_mul_coe_zeta, divideByN_one]

/-- The local squarefree weight in equation 3.2. -/
def localWeight (p : ℕ) : ℝ := if p = 2 then 1 else 2 / ((p : ℝ) - 2)

/-- The coefficient of S in equation 3.2. -/
def sieveCoeff : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).ppow 2).pmul (prodPrimeFactors localWeight)

/-- Define g by finite Mobius inversion, without an analytic identity theorem. -/
def g : ArithmeticFunction ℝ := sieveCoeff * inverseReciprocal * inverseReciprocal

/-- The coefficients d n divided by n. -/
def divisorCoeff : ArithmeticFunction ℝ := reciprocal * reciprocal

lemma g_convolution : g * divisorCoeff = sieveCoeff := by
  unfold g divisorCoeff
  calc sieveCoeff * inverseReciprocal * inverseReciprocal * (reciprocal * reciprocal) =
        sieveCoeff * (inverseReciprocal * reciprocal) * (inverseReciprocal * reciprocal) := by ring
    _ = sieveCoeff := by rw [inverse_reciprocal]; simp

lemma divisorCoeff_apply (n : ℕ) :
    divisorCoeff n = (n.divisors.card : ℝ) / n := by
  simp only [divisorCoeff, reciprocal, ← divideByN_mul, divideByN_apply]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => (ζ : ArithmeticFunction ℝ) a * (ζ : ArithmeticFunction ℝ) b)]
  congr 1
  by_cases hn : n = 0
  · subst n; simp
  · have hterm : ∀ d ∈ n.divisors,
        (ζ : ArithmeticFunction ℝ) d * (ζ : ArithmeticFunction ℝ) (n / d) = 1 := by
      intro d hd
      obtain ⟨hdiv, hn0⟩ := Nat.mem_divisors.mp hd
      have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hn0)).ne'
      have hnd0 : n / d ≠ 0 := by
        have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv)
          (Nat.pos_of_ne_zero hd0)
        omega
      simp [zeta_apply, hd0, hnd0]
    rw [sum_congr rfl hterm]
    simp

lemma sieveCoeff_apply (n : ℕ) (hn : n ≠ 0) :
    sieveCoeff n = (μ n : ℝ) ^ 2 * ∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
      2 / ((p : ℝ) - 2) := by
  simp only [sieveCoeff, pmul_apply, ppow_apply (by omega : 0 < 2),
    prodPrimeFactors_apply hn]
  congr 1
  rw [prod_filter]
  apply prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 := hprime.two_le
  by_cases h : p = 2
  · subst p; simp [localWeight]
  · have h3 : 2 < p := by omega
    simp [localWeight, h, h3]

/-- A coefficient form of equation 3.5, before summing over q. -/
theorem coefficient_identity (n : ℕ) :
    sieveCoeff n = ∑ d ∈ n.divisors,
      g d * ((n / d).divisors.card : ℝ) / ((n / d : ℕ) : ℝ) := by
  rw [← g_convolution, mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => g a * divisorCoeff b)]
  apply sum_congr rfl
  intro d _
  rw [divisorCoeff_apply]
  ring

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.divideByN_apply
#print axioms LeanLab.RieselVaughan1983.Lemma2.divideByN_mul
#print axioms LeanLab.RieselVaughan1983.Lemma2.divideByN_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.inverse_reciprocal
#print axioms LeanLab.RieselVaughan1983.Lemma2.g_convolution
#print axioms LeanLab.RieselVaughan1983.Lemma2.divisorCoeff_apply
#print axioms LeanLab.RieselVaughan1983.Lemma2.sieveCoeff_apply
#print axioms LeanLab.RieselVaughan1983.Lemma2.coefficient_identity
