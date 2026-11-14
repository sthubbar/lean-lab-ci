/-
Jia 1996 page 270, a prime pair in the distinguished region of Lemma 24.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
This is a required nonvacuity instance, not a range extension computation.
-/
import LeanLab.Languasco2004.GroupSplit548

namespace LeanLab.Languasco2004.PrimeInstance548
open Real Finset Decomp279a Decomp316c Geometry316 GroupSplit548
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 270: actual primes seven and five belong to D11 at Y equal to 1024. -/
theorem region11_prime_pair :
    Nat.Prime 7 ∧ Nat.Prime 5 ∧ regionIndex 1024 7 5 = 11 := by
  refine ⟨by decide, by decide, ?_⟩
  apply regionIndex_eq_of_mem (⟨10, by decide⟩ : Fin 69) (Y := 1024) (p := 7) (q := 5)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [regionData]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 7)
      (by norm_num : (0 : ℝ) < 63)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num
  · apply (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 7) (by positivity)
      (by norm_num : (0 : ℝ) < 57)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num
  · apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 5)
      (by norm_num : (0 : ℝ) < 30)).mp
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num
  · apply (Real.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) ≤ 5) (by positivity)
      (by norm_num : (0 : ℝ) < 24)).mp
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num

/-- Page 270 source count support: the integer 35 survives the sieve at cutoff five. -/
theorem region11_sifted_instance : 1 ≤ sifted 3 1024 38 35 5 := by
  apply Nat.succ_le_of_lt
  apply Finset.card_pos.mpr
  refine ⟨35, Finset.mem_filter.mpr ⟨by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩⟩
  intro p hp hplt hpn hpd
  have hpL := hp.two_le
  have hpU : p < 5 := by exact_mod_cast hplt
  interval_cases p <;> norm_num at *

/-- Page 270 and display 52: an actual selected region contribution is positive.
This checks the finite sum domain without any asymptotic prime theorem. -/
theorem region11_piece_positive : 0 < pieceSum 1 11 true 3 1024 38 := by
  have hlow : (1024 : ℝ) ^ (16 / 135 : ℝ) < 5 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 5)
      (by norm_num : (0 : ℝ) < 135)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024)]
    norm_num
  have hP : 7 ∈ (Finset.range (38 + 1)).filter (fun p : ℕ => p.Prime ∧
      (1024 : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * 1024)) := by
    apply Finset.mem_filter.mpr
    refine ⟨by norm_num, by decide, by linarith, ?_⟩
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hQ : 5 ∈ (Finset.range (38 + 1)).filter (fun q : ℕ => q.Prime ∧
      (1024 : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min 7 (Real.sqrt (2 * 1024 / 7))) := by
    apply Finset.mem_filter.mpr
    refine ⟨by norm_num, by decide, hlow, lt_min (by norm_num) ?_⟩
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  unfold pieceSum
  have hinner := Finset.single_le_sum
    (s := (Finset.range (38 + 1)).filter (fun q : ℕ => q.Prime ∧
      (1024 : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min 7 (Real.sqrt (2 * 1024 / 7))))
    (f := fun q : ℕ => if groupOf (regionIndex 1024 7 q) = 1 ∧
        decide (regionIndex 1024 7 q = 11) = true then
      (sifted 3 1024 38 (7 * q) q : ℝ) else 0)
    (fun q _ => by split_ifs <;> positivity) hQ
  have houter := Finset.single_le_sum
    (s := (Finset.range (38 + 1)).filter (fun p : ℕ => p.Prime ∧
      (1024 : ℝ) ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * 1024)))
    (f := fun p : ℕ => ∑ q ∈ (Finset.range (38 + 1)).filter (fun q : ℕ => q.Prime ∧
      (1024 : ℝ) ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * 1024 / (p : ℝ)))),
      if groupOf (regionIndex 1024 p q) = 1 ∧ decide (regionIndex 1024 p q = 11) = true then
        (sifted 3 1024 38 (p * q) q : ℝ) else 0)
    (fun p _ => Finset.sum_nonneg (fun q _ => by split_ifs <;> positivity)) hP
  simp only [Nat.cast_ofNat] at hinner houter
  have hi := region11_prime_pair.2.2
  have hleft : (if groupOf (regionIndex 1024 7 5) = 1 ∧
      decide (regionIndex 1024 7 5 = 11) = true then
      (sifted 3 1024 38 (7 * 5) 5 : ℝ) else 0) = (sifted 3 1024 38 35 5 : ℝ) := by
    norm_num [hi, groupOf]
  rw [hleft] at hinner
  have hc := hinner.trans houter
  have hs : (0 : ℝ) < sifted 3 1024 38 35 5 := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) region11_sifted_instance)
  exact hs.trans_le hc

#print axioms region11_prime_pair
#print axioms region11_sifted_instance
#print axioms region11_piece_positive
end
end LeanLab.Languasco2004.PrimeInstance548
