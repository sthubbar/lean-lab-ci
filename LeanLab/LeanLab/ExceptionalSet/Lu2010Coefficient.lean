/-
P0095 Lu 2010, equation 63 on page 2379 and equation 86 on page 2392.
CODEX task47, unit U-8093. AI wrote this Lean code. Binary Goldbach is open.

The modulus sum in the coefficient energy estimate.
The support condition is divisibility by the least common multiple of the conductors.
-/
import LeanLab.ExceptionalSet.Lu2010Packets
import LeanLab.ExceptionalSet.Lu2010Eq86

namespace LeanLab.ExceptionalSet.Lu2010Coefficient
open Finset
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Packets

/-- Counting the reduced numerators at each denominator. -/
theorem farey_sum_denominator (Q : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ farey Q, f p.1 = ∑ q ∈ Icc 1 Q, (q.totient : ℝ) * f q := by
  classical
  unfold farey
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro q hq
  have hqQ := (mem_Icc.mp hq).2
  rw [← sum_filter]
  have he : (range Q).filter (fun a => a < q ∧ a.Coprime q) =
      (range q).filter (fun a => q.Coprime a) := by
    ext a
    simp only [mem_filter, mem_range, Nat.coprime_comm]
    omega
  rw [he]
  simp only [Prod.fst]
  rw [sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime]

/-- A uniform bound on q over phi q gives the inverse-cube estimate. -/
theorem inv_totient_cube_le {q : ℕ} (hq : 1 ≤ q) {K : ℝ} (hK : (q : ℝ) ≤ K * q.totient) :
    1 / (q.totient : ℝ) ^ 3 ≤ K ^ 3 / (q : ℝ) ^ 3 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul, mul_pow] using pow_le_pow_left₀ hq0.le hK 3

/-- Energy of coefficients supported on multiples of one conductor pair modulus. -/
theorem coefficient_energy {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (B : ℕ × ℕ → ℂ)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hphi : ∀ q ∈ Icc 1 Q, (q : ℝ) ≤ K * q.totient)
    (hB : ∀ p ∈ farey Q, ‖B p‖ ^ 2 ≤
      if r ∣ p.1 then A / (p.1.totient : ℝ) ^ 4 else 0) :
    ∑ p ∈ farey Q, ‖B p‖ ^ 2 ≤ 2 * A * K ^ 3 / (r : ℝ) ^ 3 := by
  classical
  have h1 : (∑ p ∈ farey Q, ‖B p‖ ^ 2) ≤
      A * ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), 1 / (q.totient : ℝ) ^ 3 := by
    refine (sum_le_sum hB).trans_eq ?_
    rw [farey_sum_denominator Q (fun q => if r ∣ q then A / (q.totient : ℝ) ^ 4 else 0),
      sum_filter, mul_sum]
    apply sum_congr rfl
    intro q hq
    have hφ : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by have := (mem_Icc.mp hq).1; omega)).ne'
    by_cases hd : r ∣ q
    · simp only [hd, ite_true]
      field_simp
    · simp [hd]
  calc (∑ p ∈ farey Q, ‖B p‖ ^ 2)
      ≤ A * ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), 1 / (q.totient : ℝ) ^ 3 := h1
    _ ≤ A * ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), K ^ 3 / (q : ℝ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply sum_le_sum
      intro q hq
      have hqI := (mem_filter.mp hq).1
      exact inv_totient_cube_le (mem_Icc.mp hqI).1 (hphi q hqI)
    _ = A * K ^ 3 * ∑ q ∈ (Icc 1 Q).filter (fun q => r ∣ q), 1 / (q : ℝ) ^ 3 := by
      simp_rw [div_eq_mul_inv, ← mul_sum]
      ring
    _ ≤ A * K ^ 3 * (2 / (r : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (sum_multiples_inv_cube hr Q) (by positivity)
    _ = 2 * A * K ^ 3 / (r : ℝ) ^ 3 := by ring

/-- With the primitive Gauss factor bound A equal to r squared, the saving is inverse r. -/
theorem coefficient_energy_pair {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (B : ℕ × ℕ → ℂ)
    {K : ℝ} (hK : 0 ≤ K) (hphi : ∀ q ∈ Icc 1 Q, (q : ℝ) ≤ K * q.totient)
    (hB : ∀ p ∈ farey Q, ‖B p‖ ^ 2 ≤
      if r ∣ p.1 then (r : ℝ) ^ 2 / (p.1.totient : ℝ) ^ 4 else 0) :
    ∑ p ∈ farey Q, ‖B p‖ ^ 2 ≤ 2 * K ^ 3 / (r : ℝ) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  refine (coefficient_energy hr Q B (sq_nonneg _) hK hphi hB).trans_eq ?_
  field_simp

end LeanLab.ExceptionalSet.Lu2010Coefficient

#print axioms LeanLab.ExceptionalSet.Lu2010Coefficient.farey_sum_denominator
#print axioms LeanLab.ExceptionalSet.Lu2010Coefficient.inv_totient_cube_le
#print axioms LeanLab.ExceptionalSet.Lu2010Coefficient.coefficient_energy
#print axioms LeanLab.ExceptionalSet.Lu2010Coefficient.coefficient_energy_pair
