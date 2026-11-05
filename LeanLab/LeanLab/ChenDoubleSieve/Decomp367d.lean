import LeanLab.ChenDoubleSieve.Decomp367c
import LeanLab.ChenDoubleSieve.Decomp348v

/-!
Logarithmic coordinates for the fixed F5 integration triangle.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
These are exact finite identities, not a prime sum integral theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348

/-- A real power lower cutoff is exactly a logarithmic coordinate lower bound. -/
theorem power_cutoff_le_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (a : ℝ) :
    (N : ℝ) ^ a ≤ p ↔ a ≤ log (p : ℝ) / log N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [← log_le_log_iff (rpow_pos_of_pos hpos _) hppos, log_rpow hpos,
    le_div_iff₀ hlog]

/-- A strict real power upper cutoff is exactly a strict logarithmic bound. -/
theorem lt_power_cutoff_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (a : ℝ) :
    (p : ℝ) < (N : ℝ) ^ a ↔ log (p : ℝ) / log N < a := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [← log_lt_log_iff hppos (rpow_pos_of_pos hpos _), log_rpow hpos,
    div_lt_iff₀ hlog]

/-- The crossing upper cutoff becomes a fixed diagonal in logarithmic coordinates. -/
theorem crossing_cutoff_iff {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p ↔
      log (p : ℝ) / log N + log (q : ℝ) / log N < 1 / 3 := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [lt_div_iff₀ hppos]
  have he := lt_power_cutoff_iff hN (Nat.mul_pos hp hq) (1 / 3 : ℝ)
  rw [Nat.cast_mul, log_mul hppos.ne' hqpos.ne', add_div] at he
  norm_num [kappa1]
  simpa only [mul_comm] using he

/-- The zero loss residual level is exactly the integrand argument in equation 10.5. -/
theorem lowerLevel_zero_coordinates {N p q : ℕ} (hN : 2 ≤ N)
    (hp : 0 < p) (hq : 0 < q) :
    lowerLevel 0 N (p * q) =
      (1 / 2 - log (p : ℝ) / log N - log (q : ℝ) / log N) / kappa1 := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [lowerLevel_divisor 0 hN (Nat.mul_pos hp hq), lowerLevel_one 0 hN,
    Nat.cast_mul, log_mul hppos.ne' hqpos.ne']
  norm_num [kappa1]
  ring

/-- The actual full F5 pair domain is exactly the fixed logarithmic triangle,
with the original finite natural bounds retained. -/
theorem mem_fullPairs5_coordinates {N p q : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hq : q.Prime) :
    (p, q) ∈ fullPairs5 N ↔ p < N ∧ q < N ∧
      kappa1 ≤ log (p : ℝ) / log N ∧ log (p : ℝ) / log N < kappa2 ∧
      kappa2 ≤ log (q : ℝ) / log N ∧
      log (p : ℝ) / log N + log (q : ℝ) / log N < 1 / 3 := by
  simp only [fullPairs5, mem_filter, mem_product, Finset.mem_range, hp, hq, true_and,
    power_cutoff_le_iff hN hp.pos, lt_power_cutoff_iff hN hp.pos,
    power_cutoff_le_iff hN hq.pos, crossing_cutoff_iff hN hp.pos hq.pos]
  tauto

/-- A concrete nonempty full F5 pair domain at a modest even power of two. -/
theorem fullPairs5_instance : (3, 11) ∈ fullPairs5 262144 := by
  have he (r : ℝ) : ((262144 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ (18 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  have hlo : ((262144 : ℕ) : ℝ) ^ kappa1 ≤ 3 := by
    rw [he]
    norm_num [kappa1]
    have hs : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
      rw [← rpow_two, ← rpow_mul (by norm_num)]
      norm_num
    nlinarith [rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2 : ℝ)]
  have h4 : (4 : ℝ) ≤ ((262144 : ℕ) : ℝ) ^ kappa2 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (2 : ℝ) ≤ 18 * kappa2)
    norm_num at h
    exact h
  have h8 : ((262144 : ℕ) : ℝ) ^ kappa2 ≤ 8 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : 18 * kappa2 ≤ (3 : ℝ))
    norm_num at h
    exact h
  simp only [fullPairs5, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, hlo,
    lt_of_lt_of_le (by norm_num : (3 : ℝ) < 4) h4, h8.trans (by norm_num), ?_⟩
  rw [he]
  norm_num [kappa1]

/-- The same pair survives the exact coprimality restriction of F5. -/
theorem lowerPairs5_instance : (3, 11) ∈ lowerPairs5 262144 := by
  have he (r : ℝ) : ((262144 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ (18 * r) := by
    rw [rpow_mul (by norm_num)]
    norm_num
  have hlo : ((262144 : ℕ) : ℝ) ^ kappa1 ≤ 3 := by
    rw [he]
    norm_num [kappa1]
    have hs : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
      rw [← rpow_two, ← rpow_mul (by norm_num)]
      norm_num
    nlinarith [rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 / 2 : ℝ)]
  have h4 : (4 : ℝ) ≤ ((262144 : ℕ) : ℝ) ^ kappa2 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : (2 : ℝ) ≤ 18 * kappa2)
    norm_num at h
    exact h
  have h8 : ((262144 : ℕ) : ℝ) ^ kappa2 ≤ 8 := by
    rw [he]
    have h := rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num [kappa2] : 18 * kappa2 ≤ (3 : ℝ))
    norm_num at h
    exact h
  have h3 : Nat.Coprime 3 262144 := by
    simpa using (show Nat.Coprime 3 2 by decide).pow_right 18
  have h11 : Nat.Coprime 11 262144 := by
    simpa using (show Nat.Coprime 11 2 by decide).pow_right 18
  simp only [lowerPairs5, Wu08Sum.P2, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, h3, h11, hlo,
    lt_of_lt_of_le (by norm_num : (3 : ℝ) < 4) h4, h8.trans (by norm_num), ?_⟩
  rw [he]
  norm_num [kappa1]

end LeanLab.ChenDoubleSieve.Task367
