import LeanLab.ChenDoubleSieve.Decomp349h
import LeanLab.ChenDoubleSieve.Decomp348o

/-!
Variable cutoff Euler product preparation for Wu 2004 equation 10.3.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- The singular correction from odd prime divisors at or above a real cutoff. -/
def variableTail (N : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
    (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The singular correction from odd prime divisors below a real cutoff. -/
def variableSmall (N : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z),
    (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- The singular factor partitions at every real cutoff. -/
theorem variable_partition (N : ℕ) (z : ℝ) :
    oddFactor N = variableSmall N z * variableTail N z := by
  have he := Finset.prod_filter_mul_prod_filter_not
    (s := N.primeFactors.filter (fun p : ℕ => 2 < p))
    (p := fun p : ℕ => (p : ℝ) < z)
    (f := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))
  simpa only [Finset.filter_filter, not_lt, oddFactor, variableSmall, variableTail] using he.symm

/-- The tail correction is at least one at every cutoff. -/
theorem variableTail_one_le (N : ℕ) (z : ℝ) : 1 ≤ variableTail N z := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
  apply (le_div_iff₀ (by linarith)).2
  linarith

/-- All cutoffs above the lower band endpoint share the existing tail bound. -/
theorem variableTail_le {N : ℕ} {z : ℝ} (hz : (N : ℝ) ^ kappa1 ≤ z) :
    variableTail N z ≤ tailCorrection N := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hpN, hp2, hpz⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpN, hp2, hz.trans hpz⟩
  · intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    apply (le_div_iff₀ (by linarith)).2
    linarith

/-- The good odd primes at a variable cutoff are exactly the sieve primes. -/
theorem variable_good_set {N : ℕ} (hEven : Even N) (z : ℝ) :
    Wu41.PS N 0 z = (Wu41.PS 1 3 z).filter (fun p => p.Coprime N) := by
  ext p
  simp only [Finset.mem_filter, Wu41.mem_PS]
  constructor
  · rintro ⟨hp, _, hpz, hcop⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) hEven.two_dvd
    exact ⟨⟨hp, by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega), hpz,
      by simp⟩, hcop⟩
  · rintro ⟨⟨hp, hp3, hpz, _⟩, hcop⟩
    exact ⟨hp, by positivity, hpz, hcop⟩

/-- The omitted odd primes are exactly the prime divisors below the cutoff. -/
theorem variable_bad_set {N : ℕ} (hN : 2 ≤ N) (z : ℝ) :
    (Wu41.PS 1 3 z).filter (fun p => ¬ p.Coprime N) =
      N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z) := by
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

/-- At modulus two the density is exactly the ordinary odd prime product. -/
theorem ordinaryDensity_product (z : ℝ) :
    Task363.localDensity 2 z =
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1)) := by
  have hs : Wu41.PS 1 3 z =
      (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p) := by
    ext p
    simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨hp, hp3, hpz, _⟩
      exact ⟨hpz, hp, by exact_mod_cast hp3⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨hp, by exact_mod_cast (show 3 ≤ p by omega), hpz, by simp⟩
  have hf : (Wu41.PS 1 3 z).filter (fun p => p.Coprime 2) = Wu41.PS 1 3 z := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hm := Wu41.mem_PS.mp hp
    have hp3 : 3 ≤ p := by exact_mod_cast hm.2.1
    exact hm.1.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num : 0 < 2) h
      omega)
  unfold Task363.localDensity
  rw [variable_good_set (by norm_num : Even (2 : ℕ)), hf, hs]

/-- The ordinary real cutoff density has the exact Mertens normalization. -/
theorem ordinaryDensity_tendsto :
    Tendsto (fun z : ℝ => log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC)
      atTop (𝓝 (2 / exp eulerMascheroniConstant)) := by
  have hm := LeanLab.AlmostPrimeSums.Decomp1527c.chen_odd_product_limit_of_mertens
    LeanLab.AlmostPrimeSums.Decomp1527c.mertens_euler_product
  have ht := hm.const_mul (2 / exp eulerMascheroniConstant)
  simp only [mul_one] at ht
  apply ht.congr
  intro z
  rw [ordinaryDensity_product, exp_neg]
  field_simp [Real.exp_ne_zero, LeanLab.ChenExplicit.twinC_pos.ne']
  <;> ring

/-- The variable local product is the ordinary odd product times its small correction. -/
theorem variableDensity_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    Task363.localDensity N z = Task363.localDensity 2 z * variableSmall N z := by
  let S := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z)
  let g := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1)
  have hb := Finset.prod_filter_mul_prod_filter_not
    (s := Wu41.PS 1 3 z) (p := fun p => p.Coprime N) (f := g)
  rw [← variable_good_set hEven, variable_bad_set hN] at hb
  have hbase : (∏ p ∈ Wu41.PS 1 3 z, g p) = Task363.localDensity 2 z := by
    rw [ordinaryDensity_product]
    apply Finset.prod_congr
    · ext p
      simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
      constructor
      · rintro ⟨hp, hp3, hpz, _⟩
        exact ⟨hpz, hp, by exact_mod_cast hp3⟩
      · rintro ⟨hpz, hp, hp2⟩
        exact ⟨hp, by exact_mod_cast (show 3 ≤ p by omega), hpz, by simp⟩
    · intro p hp
      rfl
  change Task363.localDensity N z * (∏ p ∈ S, g p) = _ at hb
  rw [hbase] at hb
  have hc : (∏ p ∈ S, g p) * variableSmall N z = 1 := by
    unfold variableSmall
    change (∏ p ∈ S, g p) * (∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1
    rw [← Finset.prod_mul_distrib]
    have he : (∏ p ∈ S, g p * (((p : ℝ) - 1) / ((p : ℝ) - 2))) = ∏ _p ∈ S, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
      dsimp [g]
      field_simp [show (p : ℝ) - 1 ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]
      <;> ring
    rw [he]
    simp
  calc
    Task363.localDensity N z = Task363.localDensity N z * 1 := by ring
    _ = Task363.localDensity N z * ((∏ p ∈ S, g p) * variableSmall N z) := by rw [hc]
    _ = Task363.localDensity 2 z * variableSmall N z := by rw [← mul_assoc, hb]

/-- The full singular factor cancels after retaining the variable prime tail. -/
theorem variableDensity_tail_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    Task363.localDensity N z * variableTail N z = Task363.localDensity 2 z * oddFactor N := by
  rw [variableDensity_factor hN hEven, variable_partition N z]
  ring

/-- The variable density normalization has an exact ordinary product quotient. -/
theorem variableDensity_normalization {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    (log z * Task363.localDensity N z / CN N) * variableTail N z =
      log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC := by
  have ho : oddFactor N ≠ 0 := by have := oddFactor_one_le N; linarith
  calc
    _ = log z * (Task363.localDensity N z * variableTail N z) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by unfold CN; ring
    _ = log z * (Task363.localDensity 2 z * oddFactor N) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by rw [variableDensity_tail_factor hN hEven]
    _ = _ := by field_simp

end LeanLab.ChenDoubleSieve.Task349
