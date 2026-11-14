import LeanLab.ChenDoubleSieve.Decomp347e

/-!
The small pair compensation at the bottom of Wu 2004 page 36.
Source: https://arxiv.org/pdf/0705.1652, pages 36 and 37.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task347
open Task275 Task315
open Wu41 (S PS)

/-- The pair domain of the sealed Upsilon 5.
Source: page 35 Upsilon 5 and page 36 final display. -/
def smallPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
    (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p)

/-- The two crossing pair bands in the S1 substitution, kept together.
Source: page 36 second display before the split at rho. -/
def lowerCrossingPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
    (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ sigma2)

/-- The variable upper cutoff of Upsilon 5 is below the S1 crossing cutoff.
Source: page 36 final display and the admissible parameters on page 38. -/
theorem small_pair_cutoff (N p : ℕ) (hN : 1 ≤ N) (hp : 0 < p)
    (hKp : (N : ℝ) ^ kappa1 ≤ p) :
    (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p ≤ (N : ℝ) ^ sigma2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp)).mpr
  calc
    _ ≤ (N : ℝ) ^ (kappa1 + sigma2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa1, sigma2])
    _ = (N : ℝ) ^ kappa1 * (N : ℝ) ^ sigma2 := Real.rpow_add hNp _ _
    _ ≤ (p : ℝ) * (N : ℝ) ^ sigma2 :=
      mul_le_mul_of_nonneg_right hKp (Real.rpow_nonneg hNp.le _)
    _ = _ := mul_comm _ _

/-- Every Upsilon 5 pair lies in the combined S1 crossing band.
Source: page 36 final display, derived domain inclusion. -/
theorem smallPairs_subset (N : ℕ) (hN : 1 ≤ N) : smallPairs N ⊆ lowerCrossingPairs N := by
  intro t ht
  simp only [smallPairs, Wu08Sum.P2, mem_filter, mem_product] at ht
  obtain ⟨hNP, hp, hq, hpc, hqc, hKp, hpK, hKq, hqcut⟩ := ht
  simp only [lowerCrossingPairs, Wu08Sum.P2, mem_filter, mem_product]
  exact ⟨hNP, hp, hq, hpc, hqc, hKp, hpK, hKq,
    hqcut.trans_le (small_pair_cutoff N t.1 hN hp.pos hKp)⟩

/-- The smaller primes introduced by lowering Upsilon 5 inject into Delta one.
Source: page 36 final display and page 37 second Delta one term. -/
theorem small_pair_triple_sum_le (N : ℕ) :
    ((∑ q ∈ smallPairs N, ∑ r ∈ PS N ((N : ℝ) ^ kappa1) q.1,
      S (primeSequence N) (q.1 * q.2 * r) N r) : ℝ) ≤ tripleTerms N 1 := by
  let T := (smallPairs N).sigma (fun q => PS N ((N : ℝ) ^ kappa1) q.1)
  let e : (Σ _ : ℕ × ℕ, ℕ) → ℕ × ℕ × ℕ := fun t => (t.2, t.1.1, t.1.2)
  let f : (Σ _ : ℕ × ℕ, ℕ) → ℕ := fun t =>
    S (primeSequence N) (t.1.1 * t.1.2 * t.2) N t.2
  let g : ℕ × ℕ × ℕ → ℕ := fun t =>
    S (primeSequence N) (t.1 * t.2.1 * t.2.2) N t.1
  have hinj : Set.InjOn e T := by
    rintro ⟨⟨p, q⟩, r⟩ _ ⟨⟨p', q'⟩, r'⟩ _ he
    simp only [e, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    rfl
  have hsub : T.image e ⊆ primeTriples N (fun p q r =>
      (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ r ∧ (r : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / q) := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
    obtain ⟨hpq, hr⟩ := mem_sigma.mp hu
    simp only [smallPairs, Wu08Sum.P2, mem_filter, mem_product] at hpq
    obtain ⟨hNP, hp, hq, hpc, hqc, _, hpK, hKq, hqcut⟩ := hpq
    obtain ⟨hrp, hKr, hrp_lt, hrc⟩ := Wu41.mem_PS.mp hr
    have hrpN : u.2 < u.1.1 := by exact_mod_cast hrp_lt
    have hrN : u.2 < N := hrpN.trans (mem_range.mp hNP.1)
    simp only [e, primeTriples, mem_filter, mem_product]
    exact ⟨⟨mem_range.mpr hrN, hNP.1, hNP.2⟩,
      hrp, hp, hq, hrc, hpc, hqc, hKr, hrpN, hpK, hKq, hqcut⟩
  have hfg : ∀ u ∈ T, f u ≤ g (e u) := by
    intro u _
    dsimp only [f, g, e]
    have heq : u.1.1 * u.1.2 * u.2 = u.2 * u.1.1 * u.1.2 := by ring
    rw [heq]
  have hs := Finset.sum_le_sum_of_injOn e hinj hsub hfg (fun t _ _ => Nat.zero_le (g t))
  simp only [T, Finset.sum_sigma, f, g] at hs
  change _ ≤ ((∑ t ∈ primeTriples N (fun p q r =>
    (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2 ∧
    (N : ℝ) ^ kappa2 ≤ r ∧ (r : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / q),
      S (primeSequence N) (t.1 * t.2.1 * t.2.2) N t.1 : ℕ) : ℝ)
  exact_mod_cast hs

/-- Upsilon 5 is paid for by the combined crossing pair sum and its Delta one term.
Source: page 36 final display. The rho cutoff is enlarged to sigma two. -/
theorem small_pair_compensation (N : ℕ) (hN : 1 ≤ N) :
    sieveTerms N 5 ≤ ((∑ q ∈ lowerCrossingPairs N,
      S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) + tripleTerms N 1 := by
  have heach : ∀ q ∈ smallPairs N,
      S (primeSequence N) (q.1 * q.2) N ((N : ℝ) ^ kappa1) =
        S (primeSequence N) (q.1 * q.2) N q.1 +
        ∑ r ∈ PS N ((N : ℝ) ^ kappa1) q.1,
          S (primeSequence N) (q.1 * q.2 * r) N r := by
    intro q hq
    simp only [smallPairs, Wu08Sum.P2, mem_filter, mem_product] at hq
    obtain ⟨_, hp, hqprime, _, _, hKp, hpK, hKq, _⟩ := hq
    have hpq : q.1 < q.2 := by exact_mod_cast hpK.trans_le hKq
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      buchstab_forced_pair (primeSequence N) N q.2 q.1 hqprime hp hpq hKp
  have hid := sum_congr rfl heach
  rw [sum_add_distrib] at hid
  have hidR : sieveTerms N 5 =
      ((∑ q ∈ smallPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) +
      ((∑ q ∈ smallPairs N, ∑ r ∈ PS N ((N : ℝ) ^ kappa1) q.1,
        S (primeSequence N) (q.1 * q.2 * r) N r) : ℝ) := by
    change ((∑ q ∈ smallPairs N,
      S (primeSequence N) (q.1 * q.2) N ((N : ℝ) ^ kappa1) : ℕ) : ℝ) = _
    exact_mod_cast hid
  have hsmall : (∑ q ∈ smallPairs N, S (primeSequence N) (q.1 * q.2) N q.1) ≤
      ∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1 :=
    sum_le_sum_of_subset_of_nonneg (smallPairs_subset N hN) (fun _ _ _ => Nat.zero_le _)
  have hsmallR : ((∑ q ∈ smallPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) ≤
      ((∑ q ∈ lowerCrossingPairs N, S (primeSequence N) (q.1 * q.2) N q.1) : ℝ) := by
    exact_mod_cast hsmall
  rw [hidR]
  exact add_le_add hsmallR (small_pair_triple_sum_le N)

end LeanLab.ChenDoubleSieve.Task347
