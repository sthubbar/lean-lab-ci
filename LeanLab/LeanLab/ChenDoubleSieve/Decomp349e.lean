import LeanLab.ChenDoubleSieve.Decomp349d

/-!
Finite ordinary upper prime sums in Wu 2004 equation 10.4.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The logarithmic level perturbation is removed before prime partial summation.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The finite weighted upper prime sum for the two fixed sifting coordinates. -/
def basicUpperSum (F : ℝ → ℝ) (B : ℝ) (N : ℕ) (i : Fin 12) : ℝ :=
  ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
    F (lowerLevel B N p) / ((p : ℝ) - 1)

/-- Exact factorization of the ordinary upper main term at fixed sifting level. -/
theorem basicMain_fixed (F : ℝ → ℝ) (B : ℝ) (N : ℕ) (i : Fin 12)
    (hi : i ∈ ({2, 3} : Finset (Fin 12))) :
    basicMain F B N i =
      (N : ℝ) / log N * lowerDensity N * basicUpperSum F B N i := by
  unfold basicMain basicUpperSum
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [basicSifting_fixed N p i hi]
  change lowerDensity N / ((p : ℝ) - 1) * F (lowerLevel B N p) =
    lowerDensity N * (F (lowerLevel B N p) / ((p : ℝ) - 1))
  ring

/-- Exact normalizer quotient for either fixed upper prime sum. -/
theorem basicMain_fixed_ratio (F : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (i : Fin 12) (hi : i ∈ ({2, 3} : Finset (Fin 12))) :
    basicMain F B N i / Θ N = scaledDensity N * basicUpperSum F B N i := by
  rw [basicMain_fixed F B N i hi]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold scaledDensity Θ
  field_simp [(CN_pos N).ne', hn.ne', hl.ne']
  <;> ring

/-- Both ordinary fixed upper prime bands lie in the existing bounded mass band. -/
theorem basic_fixed_band_subset {N : ℕ} (hN : 2 ≤ N) {i : Fin 12}
    (hi : i ∈ ({2, 3} : Finset (Fin 12))) :
    Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i) ⊆ lowerPrimeBand N := by
  intro p hp
  have hs := Wu41.mem_PS.mp hp
  have he : basicEndpoint i < (1 : ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num [basicEndpoint, sigma1, sigma2]
  have hpow : (N : ℝ) ^ basicEndpoint i ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N) he.le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by exact_mod_cast hs.2.2.1.trans_le hpow), hs.1, hs.2.1⟩

/-- The reciprocal shifted prime mass of both fixed bands is uniformly bounded. -/
theorem basic_fixed_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → ∀ i : Fin 12, i ∈ ({2, 3} : Finset (Fin 12)) →
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        1 / ((p : ℝ) - 1)) ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := Task367.lowerPrimeBand_mass_bounded
  refine ⟨2 * K, by positivity, max 2 M, ?_⟩
  intro N hN i hi
  calc
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        2 * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Wu41.mem_PS.mp hp).1.two_le
      have hp0 : (0 : ℝ) < p := by linarith
      rw [mul_one_div, div_le_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) hp0]
      linarith
    _ = 2 * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        1 / (p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ p ∈ lowerPrimeBand N, 1 / (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (basic_fixed_band_subset (by omega) hi) (by intros; positivity)
    _ ≤ 2 * K := mul_le_mul_of_nonneg_left (hM N (by omega)) (by norm_num)

/-- The actual fixed upper prime sums are unchanged in the limit by removing
B from their residual levels. CONDITIONAL ON IsLinearSieve only. -/
theorem basicUpperSum_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ i : Fin 12,
      i ∈ ({2, 3} : Finset (Fin 12)) →
        |basicUpperSum F B N i - basicUpperSum F 0 N i| ≤ ε := by
  obtain ⟨K, hK, M, hM⟩ := basic_fixed_mass_bounded
  obtain ⟨J, hJ⟩ := basic_fixed_values_shift_small F f h B hB (ε / K) (by positivity)
  refine ⟨max M J, ?_⟩
  intro N hN i hi
  have he : basicUpperSum F B N i - basicUpperSum F 0 N i =
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        (F (lowerLevel B N p) - F (lowerLevel 0 N p)) / ((p : ℝ) - 1) := by
    simp only [basicUpperSum, ← Finset.sum_sub_distrib, sub_div]
  rw [he]
  calc
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        |(F (lowerLevel B N p) - F (lowerLevel 0 N p)) / ((p : ℝ) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        (ε / K) * (1 / ((p : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Wu41.mem_PS.mp hp).1.two_le
      rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ (p : ℝ) - 1)]
      simpa only [mul_one_div] using div_le_div_of_nonneg_right
        (hJ N (by omega) i hi p hp) (by linarith : 0 ≤ (p : ℝ) - 1)
    _ = (ε / K) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1)
        ((N : ℝ) ^ basicEndpoint i), 1 / ((p : ℝ) - 1) := by rw [Finset.mul_sum]
    _ ≤ (ε / K) * K := mul_le_mul_of_nonneg_left (hM N (by omega) i hi) (by positivity)
    _ = ε := by field_simp [hK.ne']

end LeanLab.ChenDoubleSieve.Task349
