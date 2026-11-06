import LeanLab.HardyLittlewood1923.Mass415
import Mathlib.Logic.Equiv.Fin.Basic

/-!
AI wrote this Lean code for CODEX task415.
P0004 page 24 section 3.14, the arithmetic square mean bound.
Equal length blocks give the same bound as the printed partial summation.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Blocks415

open Real Finset
open LeanLab.HardyLittlewood1923.Decomp415a

/-- P0004 page 24 section 3.14.
Each length n block of damped squared prime coefficients has an exponential envelope. -/
theorem prime_square_block {n : ℕ} (hn : 4 ≤ n) (k : ℕ) :
    (∑ r ∈ range n, if (k * n + r).Prime then
      Real.log (k * n + r) ^ 2 * Real.exp (-2 * (k * n + r : ℕ) / (n : ℝ)) else 0) ≤
      Real.log 4 * ((k : ℝ) + 1) ^ 2 * Real.exp (-2 * (k : ℝ)) * n * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let S := (range n).filter (fun r => (k * n + r).Prime)
  let T := S.image (fun r => k * n + r)
  have hsub : T ⊆ Nat.primesLE ((k + 1) * n) := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hm
    obtain ⟨hr, hp⟩ := mem_filter.mp hr
    exact Nat.mem_primesLE.mpr ⟨by have := mem_range.mp hr; nlinarith, hp⟩
  have hsum : (∑ r ∈ S, Real.log (k * n + r) ^ 2) =
      ∑ m ∈ T, Real.log m ^ 2 := by
    dsimp [T]
    rw [sum_image (by
      intro r hr s hs h
      change k * n + r = k * n + s at h
      omega)]
    simp only [Nat.cast_add, Nat.cast_mul]
  have he (r : ℕ) : Real.exp (-2 * (k * n + r : ℕ) / (n : ℝ)) ≤
      Real.exp (-2 * (k : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hnR]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have hM : 1 ≤ (k + 1) * n := by nlinarith
  have hlN : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hlK : Real.log ((k : ℝ) + 1) ≤ k := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (k : ℝ) + 1)
    linarith
  have hlM : Real.log (((k + 1) * n : ℕ) : ℝ) ≤ ((k : ℝ) + 1) * Real.log n := by
    push_cast
    rw [Real.log_mul (by positivity) hnR.ne']
    nlinarith [mul_le_mul_of_nonneg_left hlN (Nat.cast_nonneg (α := ℝ) k)]
  calc
    _ = ∑ r ∈ S, Real.log (k * n + r) ^ 2 * Real.exp (-2 * (k * n + r : ℕ) / (n : ℝ)) := by
      simp only [S, sum_filter]
    _ ≤ ∑ r ∈ S, Real.log (k * n + r) ^ 2 * Real.exp (-2 * (k : ℝ)) := by
      exact sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (he r) (sq_nonneg _)
    _ = (∑ r ∈ S, Real.log (k * n + r) ^ 2) * Real.exp (-2 * (k : ℝ)) := by
      rw [sum_mul]
    _ ≤ (∑ m ∈ Nat.primesLE ((k + 1) * n), Real.log m ^ 2) * Real.exp (-2 * (k : ℝ)) := by
      rw [hsum]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      exact sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ (Real.log 4 * ((k + 1) * n) * Real.log (((k + 1) * n : ℕ) : ℝ)) *
        Real.exp (-2 * (k : ℝ)) := by
      gcongr
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        Mass415.prime_square_partial_sum hM
    _ ≤ (Real.log 4 * ((k + 1) * n) * (((k : ℝ) + 1) * Real.log n)) *
        Real.exp (-2 * (k : ℝ)) := by
      gcongr
    _ = _ := by push_cast; ring

#print axioms prime_square_block

/-- P0004 page 24 section 3.14.
Summing the exponential block envelope gives the required n log n coefficient mass. -/
theorem prime_square_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      primeSquareMass n ≤ C * n * Real.log n := by
  let v : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * Real.exp (-2 * (k : ℝ))
  have hs0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 2)
  have hs1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 2)
  have hs2 := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 2)
  have hvs : Summable v := by
    apply ((hs2.add (hs1.mul_left 2)).add hs0).congr
    intro k
    dsimp [v]
    ring
  have hv0 : v 0 = 1 := by simp [v]
  have hvl : 1 ≤ ∑' k, v k := by
    rw [← hv0]
    exact hvs.le_tsum 0 (fun k _ => by dsimp [v]; positivity)
  refine ⟨Real.log 4 * (∑' k, v k), mul_pos (Real.log_pos (by norm_num))
    (lt_of_lt_of_le zero_lt_one hvl), fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  haveI : NeZero n := ⟨hnpos.ne'⟩
  let f : ℕ → ℝ := fun m =>
    if m.Prime then Real.log m ^ 2 * Real.exp (-2 * (m : ℝ) / n) else 0
  have hf : Summable f := Mass415.prime_square_mass_summable hnpos
  have hp : Summable (fun z : ℕ × Fin n => f (z.1 * n + z.2)) := by
    exact hf.comp_injective (Nat.divModEquiv n).symm.injective
  have heq : primeSquareMass n = ∑' k : ℕ, ∑ r : Fin n, f (k * n + r) := by
    calc
      _ = ∑' z : ℕ × Fin n, f (z.1 * n + z.2) :=
        ((Nat.divModEquiv n).symm.tsum_eq f).symm
      _ = _ := by rw [hp.tsum_prod]; simp only [tsum_fintype]
  have hb (k : ℕ) : (∑ r : Fin n, f (k * n + r)) ≤
      Real.log 4 * v k * n * Real.log n := by
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => f (k * n + r))]
    simpa only [f, v, Nat.cast_add, Nat.cast_mul, mul_assoc] using prime_square_block hn k
  have houter : Summable (fun k : ℕ => ∑ r : Fin n, f (k * n + r)) := by
    simpa only [tsum_fintype] using hp.prod
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, Real.log 4 * v k * n * Real.log n :=
      houter.tsum_le_tsum hb (((hvs.mul_left (Real.log 4)).mul_right (n : ℝ)).mul_right (Real.log n))
    _ = _ := by rw [tsum_mul_right, tsum_mul_right, tsum_mul_left]

#print axioms prime_square_mass_bound

end LeanLab.HardyLittlewood1923.Blocks415
