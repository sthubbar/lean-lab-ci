import LeanLab.ChenDoubleSieve.Decomp348k

/-!
Uniform large prime divisor correction in the Euler product before equation 10.2.
Source: https://arxiv.org/pdf/0705.1652, page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- The singular series factors whose primes are at or above the lower cutoff. -/
def tailCorrection (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
    (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- Every tail correction is at least one. -/
theorem tailCorrection_one_le (N : ℕ) : 1 ≤ tailCorrection N := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
  apply (le_div_iff₀ (by linarith)).2
  linarith

/-- At the fixed cutoff at most twelve factors contribute to the tail correction. -/
theorem tailCorrection_card {N : ℕ} (hN : 2 ≤ N) :
    (N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ))).card ≤ 12 := by
  have he := large_prime_divisor_card hN
    (N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)))
    (filter_subset _ _) (κ := kappa1) (by norm_num [kappa1])
    (fun p hp => (mem_filter.mp hp).2.2)
  norm_num [kappa1] at he
  exact_mod_cast he

/-- The tail correction has a uniform upper bound tending to one. -/
theorem tailCorrection_le {N : ℕ} (hN : 2 ≤ N)
    (hz : 4 ≤ (N : ℝ) ^ kappa1) :
    tailCorrection N ≤ (1 + 2 / (N : ℝ) ^ kappa1) ^ (12 : ℕ) := by
  have hzpos : 0 < (N : ℝ) ^ kappa1 := by linarith
  have he : tailCorrection N ≤ (1 + 2 / (N : ℝ) ^ kappa1) ^
      (N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ))).card := by
    calc
      _ ≤ ∏ _p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (N : ℝ) ^ kappa1 ≤ (p : ℝ)),
          (1 + 2 / (N : ℝ) ^ kappa1) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
          exact div_nonneg (by linarith) (by linarith)
        · intro p hp
          obtain ⟨_, hp2, hcut⟩ := mem_filter.mp hp
          have hp2R : (2 : ℝ) < p := by exact_mod_cast hp2
          have hid : ((p : ℝ) - 1) / ((p : ℝ) - 2) = 1 + 1 / ((p : ℝ) - 2) := by
            field_simp
            ring
          rw [hid]
          have he : 1 / ((p : ℝ) - 2) ≤ 2 / (N : ℝ) ^ kappa1 := by
            rw [div_le_div_iff₀ (by linarith) hzpos]
            linarith
          linarith
      _ = _ := by simp
  have hb : 1 ≤ 1 + 2 / (N : ℝ) ^ kappa1 := by
    have hd : 0 ≤ 2 / (N : ℝ) ^ kappa1 := by positivity
    linarith
  exact he.trans (pow_le_pow_right₀ hb (tailCorrection_card hN))

/-- Primes dividing N above the lower cutoff change the singular factor by a vanishing amount. -/
theorem tailCorrection_tendsto : Tendsto tailCorrection atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun N : ℕ => 2 / (N : ℝ) ^ kappa1) atTop (𝓝 0) := hz.const_div_atTop 2
  have hu : Tendsto (fun N : ℕ => (1 + 2 / (N : ℝ) ^ kappa1) ^ (12 : ℕ)) atTop (𝓝 1) := by
    simpa using (hr.const_add 1).pow 12
  have hs : Tendsto (fun N : ℕ => tailCorrection N - 1) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => sub_nonneg.mpr (tailCorrection_one_le N))
      _ (by simpa using hu.sub_const 1)
    filter_upwards [eventually_ge_atTop (2 : ℕ), hz.eventually_ge_atTop 4] with N hN hzN
    exact sub_le_sub_right (tailCorrection_le hN hzN) 1
  simpa using hs.add_const 1

end LeanLab.ChenDoubleSieve.Task348
