import LeanLab.ChenDoubleSieve.Decomp348m

/-!
Finite Euler product factorization for the normalization before equation 10.2.
Source: https://arxiv.org/pdf/0705.1652, page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275

/-- The product over all odd primes below the lower cutoff. -/
def baseDensity (N : ℕ) : ℝ :=
  ∏ p ∈ Wu41.PS 1 3 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))

/-- The singular series factors below the lower cutoff. -/
def smallCorrection (N : ℕ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1),
    (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- Partition the finite singular factor into small and large prime divisors. -/
theorem oddFactor_partition (N : ℕ) : oddFactor N = smallCorrection N * tailCorrection N := by
  have he := Finset.prod_filter_mul_prod_filter_not
    (s := N.primeFactors.filter (fun p : ℕ => 2 < p))
    (p := fun p : ℕ => (p : ℝ) < (N : ℝ) ^ kappa1)
    (f := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))
  simpa only [Finset.filter_filter, not_lt, oddFactor, smallCorrection, tailCorrection] using he.symm

/-- For even N the sieve primes are exactly the odd base primes coprime to N. -/
theorem density_good_set {N : ℕ} (hEven : Even N) :
    Wu41.PS N 0 ((N : ℝ) ^ kappa1) =
      (Wu41.PS 1 3 ((N : ℝ) ^ kappa1)).filter (fun p => p.Coprime N) := by
  ext p
  simp only [Finset.mem_filter, Wu41.mem_PS]
  constructor
  · rintro ⟨hp, _, hpz, hcop⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) hEven.two_dvd
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    exact ⟨⟨hp, hp3, hpz, by simp⟩, hcop⟩
  · rintro ⟨⟨hp, hp3, hpz, _⟩, hcop⟩
    exact ⟨hp, by positivity, hpz, hcop⟩

/-- The excluded odd base primes are exactly the small prime divisors of N. -/
theorem density_bad_set {N : ℕ} (hN : 2 ≤ N) :
    (Wu41.PS 1 3 ((N : ℝ) ^ kappa1)).filter (fun p => ¬ p.Coprime N) =
      N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1) := by
  ext p
  simp only [Finset.mem_filter, Wu41.mem_PS, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hp3, hpz, _⟩, hbad⟩
    have hdvd : p ∣ N := by simpa only [hp.coprime_iff_not_dvd, not_not] using hbad
    exact ⟨⟨hp, hdvd, by omega⟩, by exact_mod_cast hp3, hpz⟩
  · rintro ⟨⟨hp, hdvd, _⟩, hp2, hpz⟩
    refine ⟨⟨hp, ?_, hpz, by simp⟩, ?_⟩
    · exact_mod_cast (show 3 ≤ p by omega)
    · exact fun hc => (hp.coprime_iff_not_dvd.mp hc) hdvd

/-- The local density is the odd base product times the small singular correction. -/
theorem lowerDensity_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    lowerDensity N = baseDensity N * smallCorrection N := by
  let S := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < (N : ℝ) ^ kappa1)
  let g := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1)
  have hb := Finset.prod_filter_mul_prod_filter_not
    (s := Wu41.PS 1 3 ((N : ℝ) ^ kappa1)) (p := fun p => p.Coprime N) (f := g)
  rw [← density_good_set hEven, density_bad_set hN] at hb
  change lowerDensity N * (∏ p ∈ S, g p) = baseDensity N at hb
  have hc : (∏ p ∈ S, g p) * smallCorrection N = 1 := by
    unfold smallCorrection
    change (∏ p ∈ S, g p) * (∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1
    rw [← Finset.prod_mul_distrib]
    have he : (∏ p ∈ S, g p * (((p : ℝ) - 1) / ((p : ℝ) - 2))) = ∏ _p ∈ S, (1 : ℝ) := by
      apply prod_congr rfl
      intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.1
      dsimp [g]
      field_simp [show (p : ℝ) - 1 ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]
      <;> ring
    rw [he]
    simp
  calc
    lowerDensity N = lowerDensity N * 1 := by ring
    _ = lowerDensity N * ((∏ p ∈ S, g p) * smallCorrection N) := by rw [hc]
    _ = baseDensity N * smallCorrection N := by rw [← mul_assoc, hb]

/-- The full singular factor cancels after retaining its large prime tail. -/
theorem density_factor_identity {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    lowerDensity N * tailCorrection N = baseDensity N * oddFactor N := by
  rw [lowerDensity_factor hN hEven, oddFactor_partition]
  ring

/-- Exact cancellation in the normalized product. -/
theorem scaledDensity_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) :
    scaledDensity N * tailCorrection N =
      log N * baseDensity N / LeanLab.ChenExplicit.twinC := by
  have ho : oddFactor N ≠ 0 := by have := oddFactor_one_le N; linarith
  calc
    _ = log N * (lowerDensity N * tailCorrection N) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by unfold scaledDensity CN; ring
    _ = log N * (baseDensity N * oddFactor N) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by rw [density_factor_identity hN hEven]
    _ = _ := by field_simp

/-- The N dependent Euler product limit reduces to the ordinary odd prime product limit.
CONDITIONAL ON the explicit base product limit. -/
theorem scaledDensity_of_base
    (hbase : Tendsto (fun N : ℕ => log N * baseDensity N / LeanLab.ChenExplicit.twinC)
      evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant)))) :
    Tendsto scaledDensity evenAtTop (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) := by
  have ht := hbase.div (tendsto_inf_left tailCorrection_tendsto) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at ht
  apply ht.congr'
  change ∀ᶠ N in atTop ⊓ principal {N : ℕ | Even N}, _
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN hEven
  have htail : tailCorrection N ≠ 0 := by have := tailCorrection_one_le N; linarith
  exact ((eq_div_iff htail).2 (scaledDensity_factor hN hEven)).symm

end LeanLab.ChenDoubleSieve.Task348
