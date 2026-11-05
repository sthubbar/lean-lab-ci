import LeanLab.AlmostPrimeSums.Decomp1527c
import LeanLab.ChenDoubleSieve.Decomp348n

/-!
Supply the ordinary prime product input for Wu 2004 page 38 equation 10.2.
The existing full Mertens theorem is reused unchanged.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- The ordinary odd prime product gives the exact base density normalization. -/
theorem baseDensity_tendsto :
    Tendsto (fun N : ℕ => log N * baseDensity N / LeanLab.ChenExplicit.twinC)
      evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hm := (LeanLab.AlmostPrimeSums.Decomp1527c.chen_odd_product_limit_of_mertens
    LeanLab.AlmostPrimeSums.Decomp1527c.mertens_euler_product).comp hpow
  have hs (N : ℕ) : Wu41.PS 1 3 ((N : ℝ) ^ kappa1) =
      (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p) := by
    ext p
    simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨hp, hp3, hpz, _⟩
      exact ⟨hpz, hp, by exact_mod_cast hp3⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨hp, by exact_mod_cast (show 3 ≤ p by omega), hpz, by simp⟩
  have hprod (N : ℕ) :
      (∏ p ∈ (range ⌈(N : ℝ) ^ kappa1⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1))) = baseDensity N := by
    unfold baseDensity
    rw [hs]
  simp only [Function.comp_def] at hm
  simp_rw [hprod] at hm
  have ht := hm.const_mul (2 / (kappa1 * exp eulerMascheroniConstant))
  simp only [mul_one] at ht
  have hte := tendsto_inf_left (x₂ := principal {N : ℕ | Even N}) ht
  apply hte.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [log_rpow hpos, exp_neg]
  norm_num [kappa1]
  field_simp [Real.exp_ne_zero, LeanLab.ChenExplicit.twinC_pos.ne']
  <;> ring

/-- The exact N dependent density limit now has a supplied proof with no analytic hypothesis. -/
theorem scaledDensity_supplied :
    Tendsto scaledDensity evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) :=
  scaledDensity_of_base baseDensity_tendsto

end LeanLab.ChenDoubleSieve.Task348
#print axioms LeanLab.AlmostPrimeSums.Decomp1527c.mertens_euler_product
#print axioms LeanLab.AlmostPrimeSums.Decomp1527c.chen_odd_product_limit_of_mertens
