import Mathlib

/-!
P0099, the factorial estimates in display 24 on p. 21.
The upper estimate follows from Mathlib's sharp successive-difference bound
for the Stirling sequence and its limit.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Stirling126

open Real Filter Topology

/-- The logarithmic upper remainder in the factorial estimate of display 24, p. 21. -/
theorem log_stirlingSeq_upper {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) ≤ Real.log (√Real.pi) + 1 / (12 * n) := by
  let f : ℕ → ℝ := fun k => Real.log (Stirling.stirlingSeq (k + 1)) - 1 / (12 * (k + 1 : ℕ))
  have hm : Monotone f := by
    apply monotone_nat_of_le_succ
    intro k
    have hd := Stirling.log_stirlingSeq_sdiff_le (k + 1)
    have he : (1 : ℝ) / (12 * (k + 1 : ℕ)) - 1 / (12 * (k + 2 : ℕ)) =
        1 / (12 * (k + 1 : ℕ) * (k + 2 : ℕ)) := by
      push_cast
      field_simp
      ring
    dsimp only [f]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hd ⊢
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hd
    linarith
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)
  have hl := hs.log (show √Real.pi ≠ 0 by positivity)
  have hd : Tendsto (fun k : ℕ => (12 : ℝ) * (k + 1 : ℕ)) atTop atTop := by
    exact Filter.Tendsto.const_mul_atTop (by norm_num)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hi := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hd
  have ht : Tendsto f atTop (𝓝 (Real.log (√Real.pi))) := by
    simpa only [f, Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat, sub_zero] using hl.sub hi
  have hb := hm.ge_of_tendsto ht (n - 1)
  have he : n - 1 + 1 = n := Nat.sub_add_cancel hn
  dsimp only [f] at hb
  rw [he] at hb
  linarith

/-- The upper factorial estimate in display 24, p. 21, for every positive n. -/
theorem factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ √(2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hseq : 0 < Stirling.stirlingSeq n := by unfold Stirling.stirlingSeq; positivity
  have he := Real.exp_le_exp.mpr (log_stirlingSeq_upper hn)
  rw [Real.exp_log hseq, Real.exp_add, Real.exp_log (show 0 < √Real.pi by positivity)] at he
  rw [Stirling.stirlingSeq, div_le_iff₀ (by positivity)] at he
  have hsqrt : √(2 * Real.pi * n) = √Real.pi * √(2 * n) := by
    rw [← Real.sqrt_mul Real.pi_pos.le]
    congr 1
    ring
  calc
    (n.factorial : ℝ) ≤ √Real.pi * Real.exp (1 / (12 * n)) *
        (√(2 * n) * (n / Real.exp 1) ^ n) := he
    _ = √(2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
      rw [hsqrt]
      ring

end LeanLab.RamareSaouter2003.Stirling126
