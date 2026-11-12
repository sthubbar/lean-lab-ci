import LeanLab.ExceptionalSet.UpJ200.MinorRational446
import LeanLab.PNTPort.Vinogradov.Final

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.PrimeVaughan446`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
Real prime sums from the proved PNTPort Vaughan estimate.
Source: P0082 page 366 after display 27 and Vaughan Theorem 3.1.
Proper prime powers are controlled by Mathlib Chebyshev estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.PrimeVaughan446

open Real Finset ArithmeticFunction
open LeanLab.ExceptionalSet.U1539 (Sp eC norm_eC)

/-- P0082 page 357 prime sum definition, used on page 366.
The full prime sum norm is bounded by the Chebyshev theta function. -/
theorem full_prime_norm_le (X β : ℝ) : ‖Sp 0 X β‖ ≤ Chebyshev.theta X := by
  unfold Sp
  rw [Nat.floor_zero]
  calc
    _ ≤ ∑ n ∈ (Ioc 0 ⌊X⌋₊).filter Nat.Prime, ‖(Real.log n : ℂ) * eC (β * n)‖ :=
      norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_eC, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_natCast_nonneg _)]
      rfl

/-- P0082 page 366, conversion of Vaughan's von Mangoldt sum to primes.
The difference from the full prime sum is at most psi X minus theta X. -/
theorem full_prime_gap (X β : ℝ) :
    ‖Sp 0 X β - LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ β‖ ≤
      Chebyshev.psi X - Chebyshev.theta X := by
  have he (n : ℕ) : eC (β * n) = LeanLab.PNTPort.LargeSieve.e (n * β) := by
    unfold eC LeanLab.PNTPort.LargeSieve.e
    congr 1
    push_cast
    ring
  have hs : Icc 1 ⌊X⌋₊ = Ioc 0 ⌊X⌋₊ := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  unfold Sp LeanLab.PNTPort.Vinogradov.S Chebyshev.psi Chebyshev.theta
  rw [Nat.floor_zero, hs]
  simp_rw [sum_filter]
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  simp_rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  by_cases hp : n.Prime
  · simp only [hp, ite_eq_left, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self, norm_zero]
    simp
  · simp [hp, norm_mul, ← he, norm_eC,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- P0082 page 357, the finite lower prime cutoff.
Removing primes up to P subtracts the two full prime sums exactly. -/
theorem prime_cutoff_eq (P X β : ℝ) (hPX : P ≤ X) :
    Sp P X β = Sp 0 X β - Sp 0 P β := by
  classical
  have hp : ⌊P⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hPX
  have hu : Ioc 0 ⌊X⌋₊ = Ioc 0 ⌊P⌋₊ ∪ Ioc ⌊P⌋₊ ⌊X⌋₊ :=
    (Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hp).symm
  have hd : Disjoint ((Ioc 0 ⌊P⌋₊).filter Nat.Prime)
      ((Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hle := (mem_Ioc.mp (mem_filter.mp hn).1).2
    have hlt := (mem_Ioc.mp (mem_filter.mp hm).1).1
    omega
  unfold Sp
  simp only [Nat.floor_zero]
  rw [hu, Finset.filter_union, Finset.sum_union hd]
  abel

/-- P0082 page 366 after display 27. The prime cutoff and proper prime
powers give an explicit comparison with the PNTPort von Mangoldt sum. -/
theorem prime_cutoff_norm_le (P X β : ℝ) (hPX : P ≤ X) :
    ‖Sp P X β‖ ≤ ‖LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ β‖ +
      (Chebyshev.psi X - Chebyshev.theta X) + Chebyshev.theta P := by
  rw [prime_cutoff_eq P X β hPX]
  have hg := full_prime_gap X β
  have hf : ‖Sp 0 X β‖ ≤ ‖LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ β‖ +
      (Chebyshev.psi X - Chebyshev.theta X) := by
    have hh := norm_le_norm_sub_add (Sp 0 X β) (LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ β)
    linarith
  exact (norm_sub_le _ _).trans (add_le_add hf (full_prime_norm_le P β))

/-- P0082 page 366 after display 27, Vaughan Theorem 3.1 in real length
and real frequency form. The prime power and lower cutoff costs are explicit. -/
theorem prime_vaughan_real (P X β : ℝ) (hX : 2 ≤ X) (hP : 0 ≤ P) (hPX : P ≤ X)
    (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hqX : q ≤ ⌊X⌋₊) (hcop : Int.gcd a q = 1)
    (hap : |β - a / q| ≤ 1 / (q : ℝ) ^ 2) :
    ‖Sp P X β‖ ≤
      300 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) * (1 + Real.log X) ^ 4 +
        2 * Real.sqrt X * Real.log X + Real.log 4 * P := by
  have hN1 : 1 ≤ ⌊X⌋₊ := by
    have hh := Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ X)
    omega
  have hNX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast (show 0 < ⌊X⌋₊ by omega)
  have hX0 : 0 < X := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hL0 : 0 ≤ Real.log (⌊X⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hLX : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X := Real.log_le_log hN0 hNX
  have hs := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hap hqX
  have hsX : ‖LeanLab.PNTPort.Vinogradov.S ⌊X⌋₊ β‖ ≤
      300 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) * (1 + Real.log X) ^ 4 := by
    refine hs.trans ?_
    gcongr
  have hg := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ X)
  have ht := Chebyshev.theta_le_log4_mul_x hP
  exact (prime_cutoff_norm_le P X β hPX).trans (by gcongr)

/-- P0082 page 366 after display 27. On the literal real minor arcs,
Dirichlet approximation bounds both denominator terms by X over sqrt P. -/
theorem minor_vaughan_real (P X β : ℝ) (hX : 2 ≤ X) (hP : 1 ≤ P) (hPX : P ≤ X)
    (hminor : β ∉ LeanLab.ExceptionalSet.U1539.majorArcs P X) :
    ‖Sp P X β‖ ≤
      300 * (2 * X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * (1 + Real.log X) ^ 4 +
        2 * Real.sqrt X * Real.log X + Real.log 4 * P := by
  have hP0 : 0 < P := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨a, q, hq, hPq, hqP, hcop, hap⟩ :=
    MinorRational446.minor_rational P X β hP0 hX0 hPX hminor
  have hqX : q ≤ ⌊X⌋₊ := Nat.le_floor ((hqP.trans (div_le_self hX0.le hP)))
  have hs := prime_vaughan_real P X β hX hP0.le hPX a q hq hqX hcop hap
  have hsqP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP0
  have ht1 : X / Real.sqrt q ≤ X / Real.sqrt P :=
    div_le_div_of_nonneg_left hX0.le hsqP (Real.sqrt_le_sqrt hPq.le)
  have ht3 : Real.sqrt (X * q) ≤ X / Real.sqrt P := by
    rw [le_div_iff₀ hsqP, ← Real.sqrt_mul (by positivity)]
    have hqp : (q : ℝ) * P ≤ X := (le_div_iff₀ hP0).mp hqP
    have hm : X * q * P ≤ X ^ 2 := by nlinarith
    calc
      Real.sqrt (X * q * P) ≤ Real.sqrt (X ^ 2) := Real.sqrt_le_sqrt hm
      _ = X := Real.sqrt_sq hX0.le
  have hb : X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q) ≤
      2 * X / Real.sqrt P + X ^ (4 / 5 : ℝ) := by
    rw [show 2 * X / Real.sqrt P = X / Real.sqrt P + X / Real.sqrt P by ring]
    linarith
  exact hs.trans (by gcongr)

end LeanLab.ExceptionalSet.UpJ200.PrimeVaughan446
