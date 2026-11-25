import LeanLab.ChenDoubleSieve.Decomp349aSplitBasic

/-!
Proofs of the LEAFs `leaf_mass_one` and `leaf_mass_two_three` of Decomp349aSplitBasic,
Wu 2004 page 39, the sizes of the main terms of 10.3 and 10.4.
Source: https://arxiv.org/pdf/0705.1652.
The fixed level mass is scaledDensity times a reciprocal prime band sum, both convergent
by `scaledDensity_tendsto` and `b349_fixed_sum_tendsto`; the variable level mass of 10.3
is reduced to it because the local density is nonincreasing.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- Wu 2004 page 39, size of the main terms of 10.4 for a fixed band: the mass at the
fixed sifting level N to kappa one is O of Theta N, by the Euler product asymptotic
`scaledDensity_tendsto` and the reciprocal prime band limit `b349_fixed_sum_tendsto`
with constant weight. -/
theorem mass_fixed_band {σ : ℝ} (hκσ : kappa1 < σ) (hσ : σ < 1 / 2 - 2 * kappa1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Task363.localDensity N ((N : ℝ) ^ kappa1) / ((p : ℝ) - 1) ≤ K * Θ N := by
  have hsum := b349_fixed_sum_tendsto (F := fun _ => (1 : ℝ)) continuousOn_const 1
    one_pos hκσ hσ
  have hprod := scaledDensity_tendsto.mul (hsum.mono_left inf_le_left)
  set L := 2 / (kappa1 * exp eulerMascheroniConstant) * ∫ t in kappa1..σ, (fun _ => (1 : ℝ))
    ((1 / 2 - t) / kappa1) / t
  have hev := hprod.eventually (gt_mem_nhds (show L < |L| + 1 by
    linarith [le_abs_self L]))
  rw [evenAtTop, Filter.eventually_inf_principal, Filter.eventually_atTop] at hev
  obtain ⟨N1, hN1⟩ := hev
  refine ⟨|L| + 1, by positivity, max N1 2, fun N hEven hN => ?_⟩
  have hb := hN1 N (le_of_max_le_left hN) hEven
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hCN := CN_pos N
  have heq : (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Task363.localDensity N ((N : ℝ) ^ kappa1) / ((p : ℝ) - 1) =
      Θ N * (scaledDensity N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        (fun _ => (1 : ℝ)) (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (1 : ℝ)) / (p : ℝ)) /
          log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1)) := by
    simp only [Θ, scaledDensity, lowerDensity, Task363.localDensity, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp
  rw [heq, mul_comm _ (Θ N)]
  refine mul_le_mul_of_nonneg_left ?_ (Θ_pos hN2).le
  simpa using hb.le

/-- `leaf_mass_two_three`, exactly as stated in Decomp349aSplitBasic, Wu 2004 page 39:
the main term masses of 10.4 are O of Theta N. Proved from `mass_fixed_band`. -/
theorem leaf_mass_two_three_proved :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({2, 3} : Finset (Fin 12)) →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) ≤ K * Θ N := by
  obtain ⟨K2, hK2, M2, hM2⟩ := mass_fixed_band (σ := sigma1)
    (by norm_num [kappa1, sigma1]) (by norm_num [kappa1, sigma1])
  obtain ⟨K3, hK3, M3, hM3⟩ := mass_fixed_band (σ := sigma2)
    (by norm_num [kappa1, sigma2]) (by norm_num [kappa1, sigma2])
  refine ⟨max K2 K3, lt_max_of_lt_left hK2, max 2 (max M2 M3), fun N hEven hN i hi => ?_⟩
  have hΘ : 0 ≤ Θ N := (Θ_pos (show 2 ≤ N by omega)).le
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · have h := hM2 N hEven (by omega)
    simp only [basicEndpoint, basicSifting, show (2 : Fin 12) ≠ 1 by decide, ↓reduceIte]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hΘ)
  · have h := hM3 N hEven (by omega)
    simp only [basicEndpoint, basicSifting, show (3 : Fin 12) ≠ 1 by decide,
      show (3 : Fin 12) ≠ 2 by decide, ↓reduceIte]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hΘ)

/-- Wu 2004 page 5, the local density V z is nonincreasing in z: each new factor
1 minus 1 over p minus 1 lies in the unit interval for an odd prime p. -/
theorem localDensity_anti {N : ℕ} (hEven : Even N) {w z : ℝ} (hw : 0 ≤ w) (hwz : w ≤ z) :
    Task363.localDensity N z ≤ Task363.localDensity N w := by
  rw [Task363.localDensity_split N hw hwz]
  apply mul_le_of_le_one_right (Task363.localDensity_pos hEven w).le
  apply Finset.prod_le_one₀
  · intro p hp
    obtain ⟨hpr, _, _, hcop⟩ := Wu41.mem_PS.mp hp
    have h2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (dvd_refl 2)
        (even_iff_two_dvd.mp hEven) hcop
    have h3 : (3 : ℝ) ≤ p := by
      have := hpr.two_le
      exact_mod_cast (by omega : 3 ≤ p)
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  · intro p hp
    have h2 := (Wu41.mem_PS.mp hp).1.two_le
    have h2r : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have : 0 ≤ 1 / ((p : ℝ) - 1) := by
      apply div_nonneg zero_le_one; linarith
    linarith

/-- `leaf_mass_one`, exactly as stated in Decomp349aSplitBasic, Wu 2004 page 39:
the main term mass of 10.3 is O of Theta N. V p is at most V of N to kappa one on
the band, which reduces it to `mass_fixed_band` with upper endpoint kappa two. -/
theorem leaf_mass_one_proved :
    ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint 1),
        Task363.localDensity N (basicSifting N p 1) / ((p : ℝ) - 1) ≤ K * Θ N := by
  obtain ⟨K, hK, M, hM⟩ := mass_fixed_band (σ := kappa2)
    (by norm_num [kappa1, kappa2]) (by norm_num [kappa1, kappa2])
  refine ⟨K, hK, max 2 M, fun N hEven hN => ?_⟩
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (le_of_max_le_left hN)
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have he1 : basicEndpoint 1 = kappa2 := by simp [basicEndpoint]
  rw [he1]
  refine le_trans ?_ (hM N hEven (le_of_max_le_right hN))
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp => ?_) (by positivity)
  obtain ⟨hpr, hpw, _, _⟩ := Wu41.mem_PS.mp hp
  have h2r : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  simp only [basicSifting, ↓reduceIte]
  exact div_le_div_of_nonneg_right
    (localDensity_anti hEven (by positivity) hpw) (by linarith)

end LeanLab.ChenDoubleSieve.Task349

