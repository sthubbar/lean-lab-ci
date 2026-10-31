/-
Vaughan's Theorem 3.1 in the dft form of MVVinogradov.lean, PROVED, unit U-1147, PC run
20261020T0202Z-8791, T1, P0091 Estermann 1938 and P0003 Vinogradov 1937.

`vinogradovDFT_proved : VinogradovDFT`, unconditional. Route: the dft of `logPrimes x` at `k`
is the prime sum `Σ_{p ≤ x} log p e(p α)` with `α = -val k / M` (`dft_logPrimes_eq`); it differs
from the von Mangoldt sum `S x α` of PNTPort/Vinogradov by at most `ψ(x) - θ(x) ≤ 2 √x log x`
(Mathlib `Chebyshev.psi_sub_theta_le`); `S x α` is bounded by the lab's
`PNTPort.Vinogradov.vinogradov_minor` when the denominator is at most `x`, and the trivial
bound `θ(x) ≤ log 4 · x` covers denominators above `x`. So `estermann_of_vinogradov` now rests
on `MajorArcCount` alone: `estermann_of_majorArcCount`.

KNOWN mathematics. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.MVVinogradov
import LeanLab.PNTPort.Vinogradov.Final

open ZMod Finset Real

namespace LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

local notation "eL" => LeanLab.PNTPort.LargeSieve.e

/-- One term: `stdAddChar (-(n k)) = e(n · (-val k / M))`. -/
lemma stdAddChar_term (x n : ℕ) (k : ZMod (Mx x)) :
    (stdAddChar (-((n : ZMod (Mx x)) * k)) : ℂ) =
      eL ((n : ℝ) * (-(ZMod.val k : ℝ) / (Mx x : ℝ))) := by
  have hk : k = ((ZMod.val k : ℕ) : ZMod (Mx x)) := (ZMod.natCast_zmod_val k).symm
  have h : -((n : ZMod (Mx x)) * k) = (((-(n * ZMod.val k : ℕ) : ℤ)) : ZMod (Mx x)) := by
    conv_lhs => rw [hk]
    push_cast; ring
  rw [h, stdAddChar_apply, toCircle_intCast]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- The dft of `logPrimes x` is the prime exponential sum at `α = -val k / M`. -/
theorem dft_logPrimes_eq (x : ℕ) (k : ZMod (Mx x)) :
    𝓕 (logPrimes x) k = ∑ n ∈ (Icc 1 x).filter Nat.Prime,
      (Real.log n : ℂ) * eL ((n : ℝ) * (-(ZMod.val k : ℝ) / (Mx x : ℝ))) := by
  rw [dft_apply]
  have hsupp : ∀ j : ZMod (Mx x), j ∉ univ.filter (fun j : ZMod (Mx x) =>
      (ZMod.val j).Prime ∧ ZMod.val j ≤ x) →
      stdAddChar (-(j * k)) • logPrimes x j = 0 := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    simp [logPrimes, hj]
  rw [← Finset.sum_subset (subset_univ _) (fun j _ hj => hsupp j hj)]
  refine Finset.sum_nbij' (fun j => ZMod.val j) (fun n => (n : ZMod (Mx x))) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_coe, mem_filter, mem_univ, true_and, mem_Icc] at hj ⊢
    exact ⟨⟨hj.1.one_lt.le, hj.2⟩, hj.1⟩
  · intro n hn
    simp only [mem_coe, mem_filter, mem_Icc] at hn
    have hlt : n < Mx x := by unfold Mx; omega
    simp only [mem_coe, mem_filter, mem_univ, true_and]
    rw [ZMod.val_natCast_of_lt hlt]
    exact ⟨hn.2, hn.1.2⟩
  · intro j _
    exact ZMod.natCast_zmod_val j
  · intro n hn
    simp only [mem_coe, mem_filter, mem_Icc] at hn
    have hlt : n < Mx x := by unfold Mx; omega
    exact ZMod.val_natCast_of_lt hlt
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have hj' : j = ((ZMod.val j : ℕ) : ZMod (Mx x)) := (ZMod.natCast_zmod_val j).symm
    simp only [logPrimes, hj, and_self, if_true]
    conv_lhs => rw [hj']
    rw [smul_eq_mul, stdAddChar_term, mul_comm]
    rw [ZMod.natCast_zmod_val]

lemma norm_eL (t : ℝ) : ‖eL t‖ = 1 := by
  unfold LeanLab.PNTPort.LargeSieve.e
  rw [Complex.norm_exp]
  simp

/-- `θ` as a finite sum over `Icc 1 x` -/
lemma theta_nat_eq (x : ℕ) :
    Chebyshev.theta x = ∑ n ∈ (Icc 1 x).filter Nat.Prime, Real.log n := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast]
  congr 1

/-- Trivial bound: `‖𝓕 (logPrimes x) k‖ ≤ θ(x)`. -/
theorem norm_dft_le_theta (x : ℕ) (k : ZMod (Mx x)) :
    ‖𝓕 (logPrimes x) k‖ ≤ Chebyshev.theta x := by
  rw [dft_logPrimes_eq, theta_nat_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
  rw [norm_mul, norm_eL, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg n)]

/-- The prime sum against the von Mangoldt sum: the gap is at most `ψ(x) - θ(x)`. -/
theorem norm_dft_sub_S_le (x : ℕ) (k : ZMod (Mx x)) :
    ‖𝓕 (logPrimes x) k - LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ))‖
      ≤ Chebyshev.psi x - Chebyshev.theta x := by
  rw [dft_logPrimes_eq]
  unfold LeanLab.PNTPort.Vinogradov.S
  rw [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  have hpsi : Chebyshev.psi x = ∑ n ∈ Icc 1 x, ArithmeticFunction.vonMangoldt n := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  rw [hpsi, theta_nat_eq, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp
  · simp only [hp, if_false, zero_sub, norm_neg, sub_zero]
    rw [norm_mul, norm_eL, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- **Vaughan's Theorem 3.1 in the form `VinogradovDFT`, PROVED.** -/
theorem vinogradovDFT_proved : VinogradovDFT := by
  refine ⟨4900, 16, fun x hx k r hr => ?_⟩
  have hx16 : (16 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : (2 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num) hx16
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    nlinarith
  set q := r.den with hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast r.den_pos
  have hsq : 0 ≤ Real.sqrt ((x : ℝ) * q) := Real.sqrt_nonneg _
  have hx45 : 0 ≤ (x : ℝ) ^ (4 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hxq : 0 ≤ (x : ℝ) / Real.sqrt q := div_nonneg hx0.le (Real.sqrt_nonneg _)
  have hL4 : 16 ≤ Real.log x ^ 4 := by
    have : (2 : ℝ) ^ 4 ≤ Real.log x ^ 4 := pow_le_pow_left₀ (by norm_num) hlog 4
    linarith
  set B := (x : ℝ) / Real.sqrt q + (x : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((x : ℝ) * q) with hB
  have hB0 : 0 ≤ B := by positivity
  rcases le_or_gt q x with hqx | hqx
  · -- denominator at most x: Vinogradov
    have hcop : IsCoprime (-r.num) (q : ℤ) := by
      rw [IsCoprime.neg_left_iff]
      exact (Int.isCoprime_iff_gcd_eq_one.mpr r.reduced)
    have hα : |(-(ZMod.val k : ℝ) / (Mx x : ℝ)) - ((-r.num : ℤ) : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 := by
      have hrq : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
        rw [hq]; exact_mod_cast (Rat.num_div_den r).symm
      have : (-(ZMod.val k : ℝ) / (Mx x : ℝ)) - ((-r.num : ℤ) : ℝ) / (q : ℝ)
          = -((ZMod.val k : ℝ) / (Mx x : ℝ) - (r : ℝ)) := by
        rw [hrq]; push_cast; ring
      rw [this, abs_neg]; exact hr
    have hV := LeanLab.PNTPort.Vinogradov.vinogradov_minor (q := q) r.den_pos hcop hα
      (N := x) (by exact_mod_cast hqx)
    have hgap := norm_dft_sub_S_le x k
    have hpt : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have h1L : (1 + Real.log x) ^ 4 ≤ 16 * Real.log x ^ 4 := by
      have : 1 + Real.log x ≤ 2 * Real.log x := by linarith
      have := pow_le_pow_left₀ (by linarith) this 4
      nlinarith
    have hsqx : Real.sqrt x ≤ (x : ℝ) ^ (4 / 5 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hlogL : 2 * Real.log x ≤ Real.log x ^ 4 := by
      have h8 : 8 ≤ Real.log x ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 3
        linarith
      nlinarith
    have hsmall : 2 * Real.sqrt x * Real.log x ≤ B * Real.log x ^ 4 := by
      have h1 : 2 * Real.sqrt x * Real.log x ≤ (x : ℝ) ^ (4 / 5 : ℝ) * Real.log x ^ 4 := by
        have := Real.sqrt_nonneg (x : ℝ)
        nlinarith
      have h2 : (x : ℝ) ^ (4 / 5 : ℝ) ≤ B := by rw [hB]; linarith
      nlinarith
    have hmain : ‖LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ))‖
        ≤ 4800 * B * Real.log x ^ 4 := by
      refine hV.trans ?_
      have : (300 : ℝ) * B * (1 + Real.log x) ^ 4 ≤ 300 * B * (16 * Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left h1L (by positivity)
      rw [hB] at this ⊢
      have hs : Real.sqrt ((q : ℝ)) = Real.sqrt (r.den : ℝ) := rfl
      nlinarith
    have htri : ‖𝓕 (logPrimes x) k‖ ≤
        ‖𝓕 (logPrimes x) k - LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ))‖ +
          ‖LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ))‖ := by
      have := norm_add_le (𝓕 (logPrimes x) k -
        LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ)))
        (LeanLab.PNTPort.Vinogradov.S x (-(ZMod.val k : ℝ) / (Mx x : ℝ)))
      simpa using this
    have : ‖𝓕 (logPrimes x) k‖ ≤ 4900 * B * Real.log x ^ 4 := by nlinarith
    simpa [hB, hq] using this
  · -- denominator above x: the trivial bound
    have ht := norm_dft_le_theta x k
    have ht4 := Chebyshev.theta_le_log4_mul_x (x := (x : ℝ)) hx0.le
    have hl4 : Real.log 4 < 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have hxs : (x : ℝ) ≤ Real.sqrt ((x : ℝ) * q) := by
      rw [Real.le_sqrt' hx0]
      have : (x : ℝ) < q := by exact_mod_cast hqx
      nlinarith
    have hBx : (x : ℝ) ≤ B := by rw [hB]; linarith
    have hth : ‖𝓕 (logPrimes x) k‖ ≤ 2 * B := by nlinarith
    have hBL : 2 * B ≤ 4900 * B * Real.log x ^ 4 := by nlinarith
    have : ‖𝓕 (logPrimes x) k‖ ≤ 4900 * B * Real.log x ^ 4 := hth.trans hBL
    simpa [hB, hq] using this

/-- **Estermann 1938, CONDITIONAL ON `MajorArcCount` alone.** -/
theorem estermann_of_majorArcCount (hMa : MajorArcCount) : LogPowerSaving :=
  estermann_of_vinogradov vinogradovDFT_proved hMa

/-- **Vinogradov's minor arc bound for this data, PROVED unconditional.** -/
theorem vinogradovMinor_proved : VinogradovMinor := vinogradovMinor_of_dft vinogradovDFT_proved

end LeanLab.ExceptionalSet.MV

#print axioms LeanLab.ExceptionalSet.MV.vinogradovDFT_proved
#print axioms LeanLab.ExceptionalSet.MV.vinogradovMinor_proved
#print axioms LeanLab.ExceptionalSet.MV.estermann_of_majorArcCount
