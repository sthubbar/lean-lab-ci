import LeanLab.ExceptionalSet.BG2026MinorCont
import LeanLab.ExceptionalSet.UpJ200.Decomp371a
import LeanLab.ExceptionalSet.KernelTail385

/-! COPY for the upstream port of P0082 displays 25 to 27 into `DecompJ200`.
This file is a pruned copy of `LeanLab.ExceptionalSet.PrimeEnergy385`, keeping only the declarations used by
`Decomp467a.truncated_moment_of_karacuba`, renamed into the namespace `UpJ200` so that
`DecompJ200` can import it without an import cycle. No statement was changed.
AI wrote this Lean code. Goldbach is open. -/


/-!
The prime sum energy used before P0082 page 365 display 24.
The proof reuses BG2026.integral_double_sum and Mathlib's Chebyshev bound.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.PrimeEnergy385

open Real Finset MeasureTheory ComplexConjugate
open LeanLab.ExceptionalSet.U1539 (Sp)

/-- Parseval for the finite prime sum of P0082 page 357 and page 365. -/
theorem prime_energy (P X : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) =
      ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have he (α : ℝ) : Sp P X α = ∑ n ∈ s, (Real.log n : ℂ) * BG2026.eC (n * α) := by
    unfold Sp
    apply sum_congr rfl
    intro n hn
    unfold U1539.eC BG2026.eC
    push_cast
    ring_nf
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he2 (α : ℝ) : ((‖Sp P X α‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, ((Real.log n : ℂ) * Real.log m) *
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', he, map_sum, sum_mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [map_mul, Complex.conj_ofReal, BG2026.conj_eC]
    have hx : BG2026.eC (n * α) * BG2026.eC (-(m * α)) =
        BG2026.eC (((n - m : ℤ) : ℝ) * α) := by
      unfold BG2026.eC
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hx]
    ring
  simp_rw [he2]
  rw [BG2026.integral_double_sum]
  push_cast
  apply sum_congr rfl
  intro n hn
  rw [sum_eq_single n]
  · simp
    ring
  · intro m hm hmn
    rw [ite_eq_right (by omega)]
    simp
  · intro h
    exact absurd hn h

/-- Every unit interval has the same prime sum energy.
Source: P0082 page 365, periodicity in the estimate before display 24. -/
theorem prime_energy_shift (P X a : ℝ) :
    (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) =
      ∑ p ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime, Real.log p ^ 2 := by
  have hp : Function.Periodic (fun α => ‖Sp P X α‖ ^ 2) 1 := by
    intro α
    dsimp only
    rw [Decomp371a.Sp_periodic P X α]
  have hi : (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) =
      (∫ α in (0 : ℝ)..1, ‖Sp P X α‖ ^ 2) := by
    simpa only [zero_add] using hp.intervalIntegral_add_eq a 0
  exact hi.trans (prime_energy P X)

/-- The uniform prime sum mass bound used on P0082 page 365.
The explicit constant log 4 comes from Mathlib's Chebyshev theta bound. -/
theorem prime_energy_le (P X a : ℝ) (hX : 2 ≤ X) :
    (∫ α in a..a + 1, ‖Sp P X α‖ ^ 2) ≤ Real.log 4 * X * Real.log X := by
  classical
  rw [prime_energy_shift]
  let s := (Ioc ⌊P⌋₊ ⌊X⌋₊).filter Nat.Prime
  have hX0 : 0 ≤ X := by linarith
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hsum : (∑ p ∈ s, Real.log p) ≤ Chebyshev.theta X := by
    unfold Chebyshev.theta
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rcases mem_filter.mp hp with ⟨hI, hprime⟩
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hI).1,
        (mem_Ioc.mp hI).2⟩, hprime⟩
    · intro p hp _
      have hp1 := (mem_filter.mp hp).2.one_lt.le
      exact Real.log_nonneg (by exact_mod_cast hp1)
  have hterm (p : ℕ) (hp : p ∈ s) : Real.log p ^ 2 ≤ Real.log X * Real.log p := by
    have hprime := (mem_filter.mp hp).2
    have hLp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    have hpfloor : (p : ℝ) ≤ ⌊X⌋₊ := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hpX : (p : ℝ) ≤ X := hpfloor.trans (Nat.floor_le hX0)
    have hL := Real.log_le_log (by exact_mod_cast hprime.pos) hpX
    nlinarith [mul_nonneg hLp (sub_nonneg.mpr hL)]
  calc ∑ p ∈ s, Real.log p ^ 2 ≤ ∑ p ∈ s, Real.log X * Real.log p := sum_le_sum hterm
    _ = Real.log X * ∑ p ∈ s, Real.log p := (mul_sum _ _ _).symm
    _ ≤ Real.log X * Chebyshev.theta X := mul_le_mul_of_nonneg_left hsum hLX
    _ ≤ Real.log X * (Real.log 4 * X) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hX0) hLX
    _ = _ := by ring

/-- The prime weighted unit interval bound before P0082 page 365 display 24.
It is uniform in the real phase frequency v and in the prime lower cutoff P. -/
theorem prime_kernel_block_le (P X Δ a v : ℝ) (hX : 2 ≤ X)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (ha : 0 < a) :
    (∫ α in a..a + 1,
      ‖Sp P X α ^ 2 * (U1539.Kfun Δ α : ℂ) * U1539.eC (-(α * v))‖) ≤
        (Real.log 4 * X * Real.log X) / (Δ * (Real.pi * a) ^ 2) := by
  have hg : Continuous (fun α => Sp P X α ^ 2 * U1539.eC (-(α * v))) := by
    unfold Sp U1539.eC
    fun_prop
  have hm : (∫ α in a..a + 1, ‖Sp P X α ^ 2 * U1539.eC (-(α * v))‖) ≤
      Real.log 4 * X * Real.log X := by
    simp only [norm_mul, norm_pow, U1539.norm_eC, mul_one]
    exact prime_energy_le P X a hX
  calc (∫ α in a..a + 1,
      ‖Sp P X α ^ 2 * (U1539.Kfun Δ α : ℂ) * U1539.eC (-(α * v))‖)
      = ∫ α in a..a + 1,
          ‖(Sp P X α ^ 2 * U1539.eC (-(α * v))) * (U1539.Kfun Δ α : ℂ)‖ := by
        apply intervalIntegral.integral_congr
        intro α hα
        simp only [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ _ := KernelTail385.block_kernel_norm_le _ hg Δ a _ hΔ hΔ1 ha hm

end LeanLab.ExceptionalSet.UpJ200.PrimeEnergy385
