import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Supply split for the F4 lower bound in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equation 10.5.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task348
open Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The actual ordered coprime prime pair domain for Upsilon 4. -/
def lowerPairs4 (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2)

/-- The finite prime sum before passage to the F4 double integral. -/
def lowerSum4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ lowerPairs4 N,
    f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)

/-- The unscaled double integral in equation 10.5 for F4. -/
def lowerIntegral4 (f : ℝ → ℝ) : ℝ :=
  ∫ t in kappa1..kappa2,
    (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t

/-- The finite level main term for Upsilon 4. -/
def main4 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / log N * lowerDensity N * lowerSum4 f B N



/-! ### Mertens' second theorem in band form -/

/-- The initial segment of the reciprocal prime sum, as a sum over `Nat.primesLE`. -/
private lemma band_sum_Ioc_eq (m n : ℕ) (hmn : m ≤ n) :
    (∑ p ∈ (Finset.Ioc m n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      = (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ))
        - (∑ p ∈ Nat.primesLE m, (1 : ℝ) / (p : ℝ)) := by
  have h1 : Nat.primesLE n = (Finset.Ioc 0 n).filter Nat.Prime :=
    Nat.primesLE_eq_filter_Ioc_zero n
  have h2 : Nat.primesLE m = (Finset.Ioc 0 m).filter Nat.Prime :=
    Nat.primesLE_eq_filter_Ioc_zero m
  have hun : (Finset.Ioc 0 n).filter Nat.Prime
      = (Finset.Ioc 0 m).filter Nat.Prime ∪ (Finset.Ioc m n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h0, hn⟩, hp⟩
      by_cases h : p ≤ m
      · exact Or.inl ⟨⟨h0, h⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, hn⟩, hp⟩
    · rintro (⟨⟨h0, hm⟩, hp⟩ | ⟨⟨hm, hn⟩, hp⟩)
      · exact ⟨⟨h0, le_trans hm hmn⟩, hp⟩
      · exact ⟨⟨by omega, hn⟩, hp⟩
  have hdis : Disjoint ((Finset.Ioc 0 m).filter Nat.Prime)
      ((Finset.Ioc m n).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp hq
    omega
  rw [h1, h2, hun, Finset.sum_union hdis]
  ring

/-- The logarithmic level difference is exact. -/
private lemma loglog_rpow_sub {N : ℕ} (hN : 3 ≤ N) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    log (log ((N : ℝ) ^ b)) - log (log ((N : ℝ) ^ a)) = log b - log a := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : 0 < log (N : ℝ) := log_pos hN1
  rw [log_rpow hN0, log_rpow hN0, log_mul hb.ne' hlogN.ne', log_mul ha.ne' hlogN.ne']
  ring

/-- Mertens' second theorem, band form: the reciprocal prime sum over
`N ^ a ≤ p ≤ N ^ b` tends to `log b - log a`. -/
lemma band_prime_inv (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
        ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ)) atTop (𝓝 (log b - log a)) := by
  have hb : 0 < b := lt_trans ha hab
  set K : ℝ := eulerMascheroniConstant +
    ∑' p : Nat.Primes, (log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) with hK
  have hF : Tendsto (fun z : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / (p : ℝ)) - log (log z)) atTop (𝓝 K) :=
    LeanLab.BS2022GRH.PortedMertens.solution
  have htop_b : Tendsto (fun N : ℕ => (N : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have htop_a : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ =>
      ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ b⌋₊, (1 : ℝ) / (p : ℝ)) - log (log ((N : ℝ) ^ b)))
        - ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ a⌋₊, (1 : ℝ) / (p : ℝ))
            - log (log ((N : ℝ) ^ a)))) atTop (𝓝 0) := by
    have := hF.comp htop_b |>.sub (hF.comp htop_a)
    simpa using this
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ))
        = ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ b⌋₊, (1 : ℝ) / (p : ℝ))
            - log (log ((N : ℝ) ^ b)))
          - ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ a⌋₊, (1 : ℝ) / (p : ℝ))
              - log (log ((N : ℝ) ^ a))) + (log b - log a) := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNa : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hle : ⌊(N : ℝ) ^ a⌋₊ ≤ ⌊(N : ℝ) ^ b⌋₊ := by
      apply Nat.floor_mono
      exact (Real.rpow_le_rpow_left_iff hNa).mpr (le_of_lt hab)
    rw [band_sum_Ioc_eq _ _ hle]
    have hll := loglog_rpow_sub hN ha hb
    linarith
  have hfin : Tendsto (fun N : ℕ =>
      ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ b⌋₊, (1 : ℝ) / (p : ℝ))
          - log (log ((N : ℝ) ^ b)))
        - ((∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ a⌋₊, (1 : ℝ) / (p : ℝ))
            - log (log ((N : ℝ) ^ a)))
        + (log b - log a)) atTop (𝓝 (log b - log a)) := by
    have h := hlim.add_const (log b - log a)
    simpa using h
  exact Tendsto.congr' (hev.mono fun N h => h.symm) hfin


/-! ### Step 2: the band mass with the weight `1/(p-1)` -/

/-- Telescoping identity: `∑_{m < k ≤ n} ((k-1)⁻¹ - k⁻¹) = m⁻¹ - n⁻¹`. -/
private lemma sum_Ioc_inv_sub_pred (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Ioc m n, (((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹) = (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Ioc_succ_top hmn, ih]
      push_cast
      have hstep : ((n : ℝ) + 1 - 1) = (n : ℝ) := by ring
      rw [hstep]
      ring

/-- The band reciprocal prime sum with the weight `1/(p-1)` in place of `1/p`. -/
private lemma band_prime_inv_pred (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
        ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) - 1)) atTop (𝓝 (log b - log a)) := by
  have hmain := band_prime_inv a b ha hab
  have htop_a : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hm_atTop : Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp htop_a)
  have hinv : Tendsto (fun N : ℕ => (((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm_atTop
  have hdiff : Tendsto (fun N : ℕ =>
      ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
        ((1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hinv
    · refine Finset.sum_nonneg fun p hp => ?_
      simp only [Finset.mem_filter] at hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
      have h2 : (0 : ℝ) < (p : ℝ) := by linarith
      have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      simp only [one_div]
      exact sub_nonneg.mpr (inv_anti₀ h1 (by linarith))
    · filter_upwards [eventually_ge_atTop 2] with N hN
      set m : ℕ := ⌊(N : ℝ) ^ a⌋₊ with hm'
      set n : ℕ := ⌊(N : ℝ) ^ b⌋₊ with hn
      have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
      have h1a : (1 : ℝ) ≤ (N : ℝ) ^ a := by
        calc (1 : ℝ) = (1 : ℝ) ^ a := (one_rpow a).symm
          _ ≤ (N : ℝ) ^ a := Real.rpow_le_rpow (by norm_num) (le_of_lt hN1) (le_of_lt ha)
      have hm1 : 1 ≤ m := by
        rw [hm']
        exact Nat.le_floor (by simpa using h1a)
      have hmn : m ≤ n := by
        rw [hm', hn]
        exact Nat.floor_mono ((Real.rpow_le_rpow_left_iff hN1).mpr (le_of_lt hab))
      have hsub : (Finset.Ioc m n).filter Nat.Prime ⊆ Finset.Ioc m n :=
        Finset.filter_subset _ _
      have hbound : ∑ p ∈ (Finset.Ioc m n).filter Nat.Prime,
            ((1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ (Finset.Ioc m n).filter Nat.Prime,
              (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := by
        refine Finset.sum_le_sum fun p _ => ?_
        simp only [one_div]
        exact le_of_eq rfl
      calc ∑ p ∈ (Finset.Ioc m n).filter Nat.Prime,
              ((1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ (Finset.Ioc m n).filter Nat.Prime, (((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹) := hbound
        _ ≤ ∑ k ∈ Finset.Ioc m n, (((k : ℝ) - 1)⁻¹ - (k : ℝ)⁻¹) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
            intro x hx _
            simp only [Finset.mem_Ioc] at hx
            have hx2 : (2 : ℝ) ≤ (x : ℝ) := by
              have : 2 ≤ x := by omega
              exact_mod_cast this
            have h1 : (0 : ℝ) < (x : ℝ) - 1 := by linarith
            have h2 : (0 : ℝ) < (x : ℝ) := by linarith
            exact sub_nonneg.mpr (inv_anti₀ h1 (by linarith))
        _ = (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := sum_Ioc_inv_sub_pred m n hm1 hmn
        _ ≤ (m : ℝ)⁻¹ := by
            have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
            linarith
  have hsum : (fun N : ℕ =>
        ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) - 1))
      = fun N : ℕ =>
          (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ))
        + ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
            ((1 : ℝ) / ((p : ℝ) - 1) - (1 : ℝ) / (p : ℝ)) := by
    funext N
    rw [← Finset.sum_add_distrib]
    congr 1 with p
    ring
  rw [hsum]
  simpa using hmain.add hdiff

/-! ### Step 3: the exact pair domain and its totient weight -/

/-- Membership in the ordered coprime prime pair domain, for `N ≥ 2`. -/
private lemma mem_lowerPairs4 {N p q : ℕ} (hN : 2 ≤ N) :
    (p, q) ∈ lowerPairs4 N ↔ p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
      (N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2 := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqN : ∀ q : ℕ, (q : ℝ) < (N : ℝ) ^ kappa2 → q < N := by
    intro q hq
    have hlt : (N : ℝ) ^ kappa2 < (N : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_lt_rpow_left_iff hN1).mpr (by norm_num [kappa2])
    rw [Real.rpow_one] at hlt
    exact_mod_cast lt_trans hq hlt
  simp only [lowerPairs4, Wu08Sum.P2, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨_, _⟩, hp, hq, hcp, hcq, h1, h2, h3⟩
    exact ⟨hp, hq, hcp, hcq, h1, h2, h3⟩
  · rintro ⟨hp, hq, hcp, hcq, h1, h2, h3⟩
    have hqlt : q < N := hqN q h3
    exact ⟨⟨by omega, by omega⟩, hp, hq, hcp, hcq, h1, h2, h3⟩

/-- The totient of a product of two distinct primes is `(p-1)(q-1)`. -/
private lemma totient_mul_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p < q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr (by omega)),
    Nat.totient_prime hp, Nat.totient_prime hq]

/-! ### Step 4: the level of a pair stays in a fixed window -/

/-- On the pair domain the level `lowerLevel` lies in the fixed window `[2, 5]` once `N` is
large enough. This is what gives boundedness and uniform continuity of `f` on the levels. -/
private lemma lowerLevel_mem_window (B : ℝ) (hB : 0 < B) :
    ∃ NB : ℕ, ∀ N : ℕ, NB ≤ N → ∀ p q : ℕ, (N : ℝ) ^ kappa1 ≤ (p : ℝ) → p < q →
      (q : ℝ) < (N : ℝ) ^ kappa2 → lowerLevel B N (p * q) ∈ Set.Icc (2 : ℝ) 5 := by
  have hsmall0 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h1.comp hlog
  have hsmall : Tendsto
      (fun N : ℕ => 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h2 := hsmall0.const_mul (12 * B)
    simpa [mul_assoc] using h2
  have hev : ∀ᶠ N : ℕ in atTop,
      12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ 1 / 4 :=
    hsmall.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨NB, hNB⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 3))
  refine ⟨NB, fun N hN p q hp hpq hq => ?_⟩
  obtain ⟨hNb, hN3⟩ := hNB N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have h1logN : (1 : ℝ) < Real.log (N : ℝ) := by
    have h3log : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact lt_of_lt_of_le h3log (Real.log_le_log (by norm_num) (by exact_mod_cast hN3))
  have hloglN : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg h1logN.le
  have hp1 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos kappa1) hp
  have hq1 : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := by omega
    exact_mod_cast this
  have hpq_real : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hlogq_lt : Real.log (q : ℝ) < kappa2 * Real.log (N : ℝ) := by
    have h := Real.log_lt_log hq1 hq
    rwa [Real.log_rpow hNpos] at h
  have hlogp_lt : Real.log (p : ℝ) < kappa2 * Real.log (N : ℝ) :=
    lt_trans (Real.log_lt_log hp1 hpq_real) (by
      have h := Real.log_lt_log hq1 hq
      rwa [Real.log_rpow hNpos] at h)
  have hlogpq_ge : 2 * kappa1 * Real.log (N : ℝ) ≤ Real.log ((p : ℝ) * (q : ℝ)) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNpos kappa1) hp
    rw [Real.log_rpow hNpos] at h
    rw [Real.log_mul hp1.ne' hq1.ne']
    linarith [Real.log_lt_log hp1 hpq_real]
  have hlogpq_lt : Real.log ((p : ℝ) * (q : ℝ)) < 2 * kappa2 * Real.log (N : ℝ) := by
    rw [Real.log_mul hp1.ne' hq1.ne']
    linarith [hlogp_lt, hlogq_lt]
  have hbl : B * Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) / 48 := by
    have h1 : 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) * Real.log (N : ℝ)
        = 12 * B * Real.log (Real.log (N : ℝ)) := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_right hNb hlN.le
    rw [h1] at h3
    linarith
  have hnumpos : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ B :=
    div_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hlN B)
  have hcast : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    positivity
  have hnum : Real.log ((N : ℝ) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ B)
      = Real.log (N : ℝ) / 2 - B * Real.log (Real.log (N : ℝ)) := by
    rw [Real.log_div (Real.rpow_pos_of_pos hNpos _).ne' (Real.rpow_pos_of_pos hlN B).ne',
      Real.log_rpow hNpos, Real.log_rpow hlN]
    ring
  have hden : Real.log ((N : ℝ) ^ kappa1) = Real.log (N : ℝ) / 12 := by
    rw [Real.log_rpow hNpos]
    simp only [kappa1]
    ring
  have hlev : lowerLevel B N (p * q)
      = (Real.log (N : ℝ) / 2 - B * Real.log (Real.log (N : ℝ))
          - Real.log ((p : ℝ) * (q : ℝ))) / (Real.log (N : ℝ) / 12) := by
    unfold lowerLevel
    rw [Real.log_div hnumpos.ne' hcast.ne', hnum, hden, Nat.cast_mul]
  have hdenpos : (0 : ℝ) < Real.log (N : ℝ) / 12 := by linarith
  have hge : (2 : ℝ) ≤ (Real.log (N : ℝ) / 2 - B * Real.log (Real.log (N : ℝ))
      - Real.log ((p : ℝ) * (q : ℝ))) / (Real.log (N : ℝ) / 12) := by
    rw [le_div_iff₀ hdenpos]
    simp only [kappa1, kappa2] at hlogpq_lt
    nlinarith [hlogpq_lt, hbl, hlN]
  have hle : (Real.log (N : ℝ) / 2 - B * Real.log (Real.log (N : ℝ))
      - Real.log ((p : ℝ) * (q : ℝ))) / (Real.log (N : ℝ) / 12) ≤ 5 := by
    rw [div_le_iff₀ hdenpos]
    simp only [kappa1] at hlogpq_ge
    nlinarith [hlogpq_ge, hbl, hlN, hloglN, hB.le]
  exact ⟨by rw [hlev]; exact hge, by rw [hlev]; exact hle⟩


/-! ### The two-dimensional band comparison (analytic core)

`lowerSum4_tendsto` needs a two-dimensional band equidistribution: the pair sum with the
factorised weights `1 / ((p-1)(q-1))` against `∫∫ g`.  Mathlib has no Riemann integration,
so the comparison is built here from interval-integral additivity and a bound lemma.
These four lemmas carry no arithmetic at all and are independent of the prime sums.
-/


/-- The triangle inequality in the form both assemblies need. -/
private lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have h := abs_add_le x (-y)
  simpa [sub_eq_add_neg] using h

/-! ### Bound: an interval integral against a constant -/

private lemma abs_integral_sub_const_mul_le {g : ℝ → ℝ} {a b c C : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable g volume a b) (h : ∀ x ∈ Set.Icc a b, |g x - c| ≤ C) :
    |(∫ x in a..b, g x) - c * (b - a)| ≤ C * (b - a) := by
  have h' : ∫ x in a..b, (g x - c) = (∫ x in a..b, g x) - c * (b - a) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const]
    ring
  rw [← h']
  have hsub : ∀ x ∈ Set.uIoc a b, ‖g x - c‖ ≤ C := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs]
    exact h x (Set.Ioc_subset_Icc_self hx)
  calc ‖∫ x in a..b, (g x - c)‖ ≤ C * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hsub
    _ = C * (b - a) := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)]

/-! ### The same in two variables -/

variable {g : ℝ → ℝ → ℝ}

private lemma abs_rect_integral_sub_const_le {a b x y c C : ℝ} (hab : a ≤ b) (hxy : x ≤ y)
    (h : ∀ t ∈ Set.Icc a b, ∀ u ∈ Set.Icc x y, |g t u - c| ≤ C)
    (hint : ∀ t ∈ Set.Icc a b, IntervalIntegrable (fun u => g t u) volume x y)
    (hint2 : IntervalIntegrable (fun t => ∫ u in x..y, g t u) volume a b) :
    |(∫ t in a..b, ∫ u in x..y, g t u) - c * ((b - a) * (y - x))|
      ≤ C * ((b - a) * (y - x)) := by
  have h1 := abs_integral_sub_const_mul_le (g := fun t => ∫ u in x..y, g t u) hab hint2
    (c := c * (y - x)) (C := C * (y - x))
    (fun t ht => abs_integral_sub_const_mul_le hxy (hint t ht) (fun u hu => h t ht u hu))
  simpa [mul_assoc, mul_comm, mul_left_comm] using h1

/-! ### The grid identity for an iterated integral -/

private lemma square_integral_eq_band_sum {a b : ℝ} {K : ℕ}
    (r : ℕ → ℝ) (hr0 : r 0 = a) (hrK : r K = b)
    (hg : Continuous (Function.uncurry g)) :
    (∫ t in a..b, ∫ u in a..b, g t u)
      = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
          ∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u := by
  have hginner : Continuous fun t : ℝ => ∫ u in a..b, g t u :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg a b
  have hpiece : ∀ j : ℕ, Continuous fun t : ℝ => ∫ u in r j..r (j + 1), g t u :=
    fun j => intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg _ _
  have hout := intervalIntegral.sum_integral_adjacent_intervals (a := r) (n := K)
    (f := fun t : ℝ => ∫ u in a..b, g t u)
    (fun k _ => hginner.intervalIntegrable (μ := volume) _ _)
  rw [hr0, hrK] at hout
  rw [← hout]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpt : ∀ t : ℝ, (∫ u in a..b, g t u)
      = ∑ j ∈ Finset.range K, ∫ u in r j..r (j + 1), g t u := by
    intro t
    have := (intervalIntegral.sum_integral_adjacent_intervals (a := r) (n := K)
      (f := fun u : ℝ => g t u)
      (fun k _ => (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable
        (μ := volume) _ _)).symm
    rwa [hr0, hrK] at this
  calc ∫ t in r i..r (i + 1), ∫ u in a..b, g t u
      = ∫ t in r i..r (i + 1), ∑ j ∈ Finset.range K, ∫ u in r j..r (j + 1), g t u := by
        exact intervalIntegral.integral_congr (fun t _ => hpt t)
    _ = ∑ j ∈ Finset.range K, ∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u :=
        intervalIntegral.integral_finsetSum (fun j _ => (hpiece j).intervalIntegrable (μ := volume) _ _)



/-! ### The band comparison: a partition's rectangle areas against the integral -/

private lemma band_sum_sub_integral_le {a b C : ℝ} {K : ℕ} (r : ℕ → ℝ)
    (hr0 : r 0 = a) (hrK : r K = b) (hmono : ∀ i, r i ≤ r (i + 1))
    (c : ℕ → ℕ → ℝ) {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g))
    (h : ∀ i < K, ∀ j < K, ∀ t ∈ Set.Icc (r i) (r (i + 1)), ∀ u ∈ Set.Icc (r j) (r (j + 1)),
      |g t u - c i j| ≤ C) :
    |(∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        c i j * ((r (i + 1) - r i) * (r (j + 1) - r j)))
      - (∫ t in a..b, ∫ u in a..b, g t u)| ≤ C * ((b - a) * (b - a)) := by
  have hint : ∀ (i j : ℕ) (u : ℝ),
      IntervalIntegrable (fun t => g t u) volume (r i) (r (i + 1)) := fun i j u =>
    (hg.comp (continuous_id.prodMk continuous_const)).intervalIntegrable (μ := volume) _ _
  have hint2 : ∀ i j : ℕ,
      IntervalIntegrable (fun t => ∫ u in r j..r (j + 1), g t u) volume (r i) (r (i + 1)) :=
    fun i j => (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg _ _
      ).intervalIntegrable (μ := volume) _ _
  have hsplit : (∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
        c i j * ((r (i + 1) - r i) * (r (j + 1) - r j)))
      - (∫ t in a..b, ∫ u in a..b, g t u)
      = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.range K,
          (c i j * ((r (i + 1) - r i) * (r (j + 1) - r j))
            - ∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u) := by
    rw [square_integral_eq_band_sum r hr0 hrK hg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_sub_distrib]
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hstep : ∀ i ∈ Finset.range K,
      |∑ j ∈ Finset.range K,
          (c i j * ((r (i + 1) - r i) * (r (j + 1) - r j))
            - ∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u)|
        ≤ ∑ j ∈ Finset.range K, C * ((r (i + 1) - r i) * (r (j + 1) - r j)) := by
    intro i hi
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hiK : i < K := Finset.mem_range.1 hi
    have hjK : j < K := Finset.mem_range.1 hj
    have hrect := abs_rect_integral_sub_const_le (g := g) (a := r i) (b := r (i + 1))
      (x := r j) (y := r (j + 1)) (c := c i j) (C := C) (hmono i) (hmono j)
      (fun t ht u hu => h i hiK j hjK t ht u hu)
      (fun t _ => (hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable
        (μ := volume) _ _) (hint2 i j)
    calc |c i j * ((r (i + 1) - r i) * (r (j + 1) - r j))
          - ∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u|
        = |(∫ t in r i..r (i + 1), ∫ u in r j..r (j + 1), g t u)
            - c i j * ((r (i + 1) - r i) * (r (j + 1) - r j))| := abs_sub_comm _ _
      _ ≤ C * ((r (i + 1) - r i) * (r (j + 1) - r j)) := hrect
  refine (Finset.sum_le_sum hstep).trans ?_
  have htel : ∀ m : ℕ, ∑ i ∈ Finset.range m, (r (i + 1) - r i) = r m - r 0 := by
    intro m
    rw [Finset.sum_range_sub]
  have htelK : ∑ i ∈ Finset.range K, (r (i + 1) - r i) = b - a := by
    rw [htel K, hr0, hrK]
  have hrow : ∀ i : ℕ, ∑ j ∈ Finset.range K, C * ((r (i + 1) - r i) * (r (j + 1) - r j))
      = (C * (r (i + 1) - r i)) * (b - a) := by
    intro i
    have h1 : ∑ j ∈ Finset.range K, C * ((r (i + 1) - r i) * (r (j + 1) - r j))
        = C * (r (i + 1) - r i) * ∑ j ∈ Finset.range K, (r (j + 1) - r j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, htelK]
  simp only [hrow]
  have hlast : ∑ i ∈ Finset.range K, (C * (r (i + 1) - r i)) * (b - a)
      = C * ((b - a) * (b - a)) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, htelK]
    ring
  rw [hlast]



/-! ## This session's work (2026-11-06T23:50Z onwards).
Everything above this line is the earlier run's `-wip-2230Z.lean` verbatim. -/

/-- Product monotonicity against a constant, by hand (this Mathlib has no usable
`Finset.prod_le_prod` for `ℝ`). -/
private lemma prod_const_le_prod_real {s : Finset ℕ} {f : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ s, M ≤ f i) : M ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx, mul_comm (f x)]
      have hcast : M ^ (s.card + 1) = M ^ s.card * M := by ring
      rw [hcast]
      have hxs : M ≤ f x := h x (Finset.mem_insert_self x s)
      have hrest : ∀ i ∈ s, M ≤ f i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hprod : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => le_trans hM (hrest i hi)
      exact mul_le_mul (ih hrest) hxs hM hprod

/-- Primes above `N^a` that divide `N` carry vanishing reciprocal mass. -/
private lemma primeFactors_ge_sum_small (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      ∑ p ∈ N.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ a ≤ (p : ℝ)),
          (1 : ℝ) / ((p : ℝ) - 1) ≤ (1 / a) / ((N : ℝ) ^ a - 1) := by
  have hbig : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_ge_atTop 2, hbig] with N hN hNa
  classical
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hM1 : (1 : ℝ) < (N : ℝ) ^ a := lt_of_lt_of_le one_lt_two hNa
  have hM0 : (0 : ℝ) < (N : ℝ) ^ a := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogM : Real.log ((N : ℝ) ^ a) = a * Real.log (N : ℝ) := Real.log_rpow hN0 a
  set T : Finset ℕ := N.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ a ≤ (p : ℝ)) with hT
  have hmem : ∀ p ∈ T, p.Prime ∧ p ∣ N ∧ (N : ℝ) ^ a ≤ (p : ℝ) := by
    intro p hp
    rw [hT, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
  have hsub : T ⊆ N.primeFactors := by rw [hT]; exact Finset.filter_subset _ _
  have hdvd : ∏ p ∈ T, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset T N.primeFactors (fun p : ℕ => p) hsub).trans
      N.prod_primeFactors_dvd
  have hprodle : ∏ p ∈ T, p ≤ N := Nat.le_of_dvd (by omega) hdvd
  have hkey : ((N : ℝ) ^ a) ^ T.card ≤ (N : ℝ) := by
    have h1 : ((N : ℝ) ^ a) ^ T.card ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
      have h := prod_const_le_prod_real (s := T) (f := fun p : ℕ => (p : ℝ))
        (M := (N : ℝ) ^ a) hM0.le (fun p hp => (hmem p hp).2.2)
      simpa using h
    have h2 : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hprodle
    linarith
  have hlogkey : (T.card : ℝ) * (a * Real.log (N : ℝ)) ≤ Real.log (N : ℝ) := by
    have h1 : Real.log (((N : ℝ) ^ a) ^ T.card) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) hkey
    rwa [Real.log_pow, hlogM] at h1
  have hcard : (T.card : ℝ) ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    nlinarith [hlogkey, hlogN]
  have hterm : ∀ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / ((N : ℝ) ^ a - 1) := by
    intro p hp
    have hpM : (N : ℝ) ^ a ≤ (p : ℝ) := (hmem p hp).2.2
    have hden : (0 : ℝ) < (N : ℝ) ^ a - 1 := by linarith
    exact one_div_le_one_div_of_le hden (by linarith)
  have hsum : ∑ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) ≤ (T.card : ℝ) * (1 / ((N : ℝ) ^ a - 1)) := by
    calc ∑ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) ≤ ∑ _p ∈ T, 1 / ((N : ℝ) ^ a - 1) :=
          Finset.sum_le_sum hterm
      _ = (T.card : ℝ) * (1 / ((N : ℝ) ^ a - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hden1 : (0 : ℝ) < (N : ℝ) ^ a - 1 := by linarith
  have hstep : (T.card : ℝ) * (1 / ((N : ℝ) ^ a - 1)) ≤ (1 / a) * (1 / ((N : ℝ) ^ a - 1)) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  calc ∑ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)
      ≤ (T.card : ℝ) * (1 / ((N : ℝ) ^ a - 1)) := hsum
    _ ≤ (1 / a) * (1 / ((N : ℝ) ^ a - 1)) := hstep
    _ = (1 / a) / ((N : ℝ) ^ a - 1) := by ring

/-- The band reciprocal prime mass is unchanged when only primes coprime to `N` are kept. -/
private lemma band_prime_inv_pred_coprime (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
        ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
      atTop (𝓝 (log b - log a)) := by
  have hmain := band_prime_inv_pred a b ha hab
  have htop_a : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (1 / a) / ((N : ℝ) ^ a - 1)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun N : ℕ => (N : ℝ) ^ a - 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-1) htop_a
    have h2 := hsub.inv_tendsto_atTop.const_mul (1 / a)
    simpa [div_eq_mul_inv] using h2
  have hnonneg_band : ∀ N : ℕ,
      ∀ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
        (0 : ℝ) ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
    intro N p hp
    rw [Finset.mem_filter] at hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hdiff : Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / ((p : ℝ) - 1))
        - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
            (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hsmall
    · -- nonneg: the coprime part is a sub-sum of the prime band
      have hsub : (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N)
          ⊆ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime := by
        intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hnonneg_band N x hx)
      linarith
    · filter_upwards [primeFactors_ge_sum_small a ha, eventually_ge_atTop 2] with N hNsum hN
      set A : Finset ℕ := (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime with hA
      have hsplit : (∑ p ∈ A, (1 : ℝ) / ((p : ℝ) - 1))
          - (∑ p ∈ A.filter (fun p => p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
          = ∑ p ∈ A.filter (fun p => ¬ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1) := by
        have := Finset.sum_filter_add_sum_filter_not (s := A) (p := fun p => p.Coprime N)
          (f := fun p : ℕ => (1 : ℝ) / ((p : ℝ) - 1))
        linarith
      have hfil : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
            (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
          = ∑ p ∈ A.filter (fun p => p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1) := by
        rw [hA, Finset.filter_filter]
      have hsub2 : A.filter (fun p => ¬ p.Coprime N)
          ⊆ N.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ a ≤ (p : ℝ)) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hA', hnc⟩ := hp
        rw [hA, Finset.mem_filter, Finset.mem_Ioc] at hA'
        obtain ⟨⟨hm, -⟩, hpp⟩ := hA'
        have hdvd : p ∣ N := (Nat.Prime.dvd_iff_not_coprime hpp).mpr hnc
        have hpge : (N : ℝ) ^ a ≤ (p : ℝ) := by
          have h1 : ⌊(N : ℝ) ^ a⌋₊ + 1 ≤ p := by omega
          have h2 : ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
          have h3 : (N : ℝ) ^ a < ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
          linarith
        rw [Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hpp, hdvd, by omega⟩, hpge⟩
      have hnn : ∀ p ∈ N.primeFactors.filter (fun p : ℕ => (N : ℝ) ^ a ≤ (p : ℝ)),
          (0 : ℝ) ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
        intro p hp
        rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.1.two_le
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      have hfin : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
            (1 : ℝ) / ((p : ℝ) - 1))
          - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
              (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
          ≤ (1 / a) / ((N : ℝ) ^ a - 1) := by
        rw [show (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
              (1 : ℝ) / ((p : ℝ) - 1)) = ∑ p ∈ A, (1 : ℝ) / ((p : ℝ) - 1) from rfl, hfil,
          hsplit]
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x hx _ => hnn x hx)).trans hNsum
      exact hfin
  have hsum : (fun N : ℕ =>
        ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
      = fun N : ℕ =>
          (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
            (1 : ℝ) / ((p : ℝ) - 1))
        - ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
            (1 : ℝ) / ((p : ℝ) - 1))
          - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
              (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) := by
    funext N; ring
  rw [hsum]
  simpa using hmain.sub hdiff

/-! ### Tools for the uniform band lemma -/

/-- A finite family of eventual statements is eventually simultaneous. -/
private lemma eventually_forall_finset {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∀ᶠ N : ℕ in atTop, P i N) : ∀ᶠ N : ℕ in atTop, ∀ i ∈ s, P i N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      have h1 : ∀ᶠ N : ℕ in atTop, P x N := h x (Finset.mem_insert_self x s)
      have h2 : ∀ᶠ N : ℕ in atTop, ∀ i ∈ s, P i N :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine (h1.and h2).mono ?_
      intro N hN
      rw [Finset.forall_mem_insert]
      exact hN

/-- A chain of integer cutoffs splits the sum over `Ioc (m 0) x`. -/
private lemma sum_Ioc_chain {f : ℕ → ℝ} {m : ℕ → ℕ} {x : ℕ} :
    ∀ J : ℕ, (∀ i < J, m i ≤ m (i + 1)) → m J ≤ x →
      ∑ k ∈ Finset.Ioc (m 0) x, f k
        = ∑ i ∈ Finset.range J, ∑ k ∈ Finset.Ioc (m i) (m (i + 1)), f k
          + ∑ k ∈ Finset.Ioc (m J) x, f k := by
  intro J
  induction J with
  | zero => intro _ _; simp
  | succ J ih =>
      intro hmono hJ
      have hmonoJ : ∀ i < J, m i ≤ m (i + 1) := fun i hi => hmono i (by omega)
      have hJx : m J ≤ x := (hmono J (by omega)).trans hJ
      rw [ih hmonoJ hJx, Finset.sum_range_succ]
      have hunion : Finset.Ioc (m J) x
          = Finset.Ioc (m J) (m (J + 1)) ∪ Finset.Ioc (m (J + 1)) x := by
        rw [Finset.Ioc_union_Ioc_eq_Ioc (hmono J (by omega)) hJ]
      have hdisj : Disjoint (Finset.Ioc (m J) (m (J + 1))) (Finset.Ioc (m (J + 1)) x) := by
        rw [Finset.disjoint_left]
        intro k hk hk'
        rw [Finset.mem_Ioc] at hk hk'
        omega
      rw [hunion, Finset.sum_union hdisj]
      ring
/-- `CumMass` converges to the logarithmic length of the window. -/
private lemma CumMass_tendsto (a : ℝ) (ha : 0 < a) {x : ℝ} (hax : a < x) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ x⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) atTop (𝓝 (Real.log x - Real.log a)) :=
  band_prime_inv_pred_coprime a x ha hax

/-! ### The uniform band lemma -/
/-- Floor slack: `log x - log ⌊x⌋ ≤ 2 / ⌊x⌋` for `x ≥ 2`. -/
private lemma log_sub_log_floor_le {x : ℝ} (hx : 2 ≤ x) :
    Real.log x - Real.log (⌊x⌋₊ : ℝ) ≤ 2 / (⌊x⌋₊ : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hfx1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have h : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith : ((1 : ℕ) : ℝ) ≤ x)
    exact_mod_cast h
  have hfx0 : 0 < (⌊x⌋₊ : ℝ) := by linarith
  have h1 : Real.log x - Real.log (⌊x⌋₊ : ℝ) = Real.log (x / ⌊x⌋₊) := by
    rw [Real.log_div hx0.ne' hfx0.ne']
  have hu : 0 < x / (⌊x⌋₊ : ℝ) := by positivity
  have h4 : x - (⌊x⌋₊ : ℝ) < 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  calc Real.log x - Real.log (⌊x⌋₊ : ℝ) = Real.log (x / ⌊x⌋₊) := h1
    _ ≤ x / ⌊x⌋₊ - 1 := Real.log_le_sub_one_of_pos hu
    _ = (x - ⌊x⌋₊) / ⌊x⌋₊ := by field_simp
    _ ≤ 1 / ⌊x⌋₊ := div_le_div_of_nonneg_right h4.le hfx0.le
    _ ≤ 2 / ⌊x⌋₊ := div_le_div_of_nonneg_right (by norm_num) hfx0.le

/-- Weighted interval comparison: `|∫ g x / x - c (log b - log a)| ≤ C (log b - log a)`. -/
private lemma abs_integral_div_sub_const_le {g : ℝ → ℝ} {a b c C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) (h : ∀ x ∈ Set.Icc a b, |g x - c| ≤ C) :
    |(∫ x in a..b, g x / x) - c * (Real.log b - Real.log a)| ≤ C * (Real.log b - Real.log a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have huicc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hneI : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [huicc]
    exact fun h => absurd h.1 (not_le.mpr ha)
  have hcontu : ContinuousOn (fun x => g x / x) (Set.uIcc a b) := by
    rw [huicc]; exact hg.div continuousOn_id hneI
  have hcontcu : ContinuousOn (fun x => c / x) (Set.uIcc a b) := by
    rw [huicc]; exact continuousOn_const.div continuousOn_id hneI
  have hcint : (∫ x in a..b, c / x) = c * (Real.log b - Real.log a) := by
    have hcongr : ∀ x ∈ Set.uIcc a b, c / x = c * x⁻¹ := fun x _ => by ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']
  have hkey : (∫ x in a..b, g x / x) - c * (Real.log b - Real.log a)
      = ∫ x in a..b, (g x - c) / x := by
    rw [← hcint]
    have hsplit : ∀ x ∈ Set.uIcc a b, (g x - c) / x = g x / x - c / x := by
      intro x hx
      field_simp
    rw [intervalIntegral.integral_congr hsplit]
    exact (intervalIntegral.integral_sub hcontu.intervalIntegrable
      hcontcu.intervalIntegrable).symm
  rw [hkey]
  have hbound : ∀ t ∈ Set.Ioc a b, ‖(g t - c) / t‖ ≤ C / t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right (h t (Set.Ioc_subset_Icc_self ht)) ht0.le
  have hCint : (∫ x in a..b, C / x) = C * (Real.log b - Real.log a) := by
    have hcongr : ∀ x ∈ Set.uIcc a b, C / x = C * x⁻¹ := fun x _ => by ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha hb, Real.log_div hb.ne' ha.ne']
  have hci : IntervalIntegrable (fun x => C / x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huicc]; exact continuousOn_const.div continuousOn_id hneI
  calc ‖∫ x in a..b, (g x - c) / x‖ ≤ ∫ x in a..b, C / x :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (by filter_upwards with t ht using hbound t ht) hci
    _ = C * (Real.log b - Real.log a) := hCint
private lemma CumMass_eq_CumInt (a : ℝ) (N : ℕ) (x : ℝ) :
    (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ x⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ x⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := rfl

/-- Splitting the cumulative mass at an intermediate cutoff. -/
private lemma CumInt_sub (a : ℝ) (N : ℕ) {p q : ℕ} (hp : ⌊(N : ℝ) ^ a⌋₊ ≤ p) (hpq : p ≤ q) :
    (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ q).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ p).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
      = ∑ k ∈ (Finset.Ioc p q).filter (fun k => k.Prime ∧ k.Coprime N),
          (1 : ℝ) / ((k : ℝ) - 1) := by
  have hunion : Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ q
      = Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ p ∪ Finset.Ioc p q :=
    (Finset.Ioc_union_Ioc_eq_Ioc hp hpq).symm
  rw [hunion, Finset.filter_union, Finset.sum_union, add_sub_cancel_left]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hx'
  omega

/-- The cumulative mass is monotone in the cutoff. -/
private lemma CumMass_mono (a : ℝ) (N : ℕ) (hN : 1 ≤ N) {x₁ x₂ : ℝ} (h : x₁ ≤ x₂) :
    (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ x₁⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) ≤ (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ x₂⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => ?_)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    have h5 : (N : ℝ) ^ x₁ ≤ (N : ℝ) ^ x₂ := by
      rcases lt_or_eq_of_le hN with hN1 | hN1
      · exact (Real.rpow_le_rpow_left_iff (by exact_mod_cast hN1 : (1 : ℝ) < N)).mpr h
      · have h1' : (N : ℝ) = 1 := by exact_mod_cast hN1.symm
        rw [h1']
        simp
    have h6 : ⌊(N : ℝ) ^ x₁⌋₊ ≤ ⌊(N : ℝ) ^ x₂⌋₊ := Nat.floor_mono h5
    exact ⟨⟨h1, h2.trans h6⟩, h3⟩
  · obtain ⟨-, hkp, -⟩ := Finset.mem_filter.mp hx
    have h2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hkp.two_le
    have : (0 : ℝ) < (x : ℝ) - 1 := by linarith
    positivity

/-- A weighted finite sum compared with a constant: `|∑ f w - c ∑ w| ≤ eu ∑ w` when
`|f - c| ≤ eu` on the support and the weights are nonnegative. -/
private lemma abs_sum_mul_sub_const_mul_le {ι : Type*} (S : Finset ι) (f w : ι → ℝ)
    {c eu : ℝ} (hw : ∀ k ∈ S, 0 ≤ w k) (h : ∀ k ∈ S, |f k - c| ≤ eu) :
    |(∑ k ∈ S, f k * w k) - c * (∑ k ∈ S, w k)| ≤ eu * (∑ k ∈ S, w k) := by
  have hR : c * (∑ k ∈ S, w k) = ∑ k ∈ S, c * w k := Finset.mul_sum ..
  have hR2 : eu * (∑ k ∈ S, w k) = ∑ k ∈ S, eu * w k := Finset.mul_sum ..
  rw [hR, hR2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [show f k * w k - c * w k = (f k - c) * w k by ring, abs_mul, abs_of_nonneg (hw k hk)]
  exact mul_le_mul_of_nonneg_right (h k hk) (hw k hk)

set_option maxHeartbeats 4000000 in
/-- **Uniform band equidistribution.** For a continuous `h` on `[a/2, 2b]`, the band prime mass
against `h (log p / log N + β)` converges to `∫_a^y h (x + β) / x` uniformly in the shift
`β ∈ [a,b]` and the upper endpoint `y ∈ [a,b]`. -/
private lemma band_uniform_add (a b : ℝ) (ha : 0 < a) (hab : a < b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc (a / 2) (3 * b))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ β ∈ Set.Icc (-(a / 2)) b, ∀ y ∈ Set.Icc a b,
      |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
            (fun p => p.Prime ∧ p.Coprime N),
          h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..y, h (xx + β) / xx| ≤ ε := by
  have hb : 0 < b := ha.trans hab
  have ha2 : 0 < a / 2 := by linarith
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  obtain ⟨C, hC1, habsC⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ Set.Icc (a / 2) (3 * b), |h x| ≤ C :=
    ⟨max C0 1, le_max_right _ _, fun x hx => by
      have h1 := hC0 x hx
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_max_left _ _)⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  set L : ℝ := Real.log b - Real.log a with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact sub_pos.mpr (Real.log_lt_log ha hab)
  set eu : ℝ := ε / (100 * C * (L + 1)) with heuval
  have heupos : 0 < eu := by rw [heuval]; positivity
  have heuL : eu * (L + 1) ≤ ε / 100 := by
    have h1 : eu * (L + 1) = ε / (100 * C) := by
      rw [heuval]; field_simp
    rw [h1]
    exact div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hh) eu heupos
  -- the mesh
  have hex : ∃ K : ℕ, 0 < K ∧ (b - a) / K ≤ min (δ / 2) (ε * a / (100 * C * (L + 1))) := by
    set η : ℝ := min (δ / 2) (ε * a / (100 * C * (L + 1))) with hη
    have hηpos : 0 < η := lt_min (by linarith) (by positivity)
    obtain ⟨K, hK⟩ := exists_nat_gt ((b - a) / η)
    have hKpos : 0 < K := by
      have h1 : 0 < (b - a) / η := div_pos (by linarith) hηpos
      have h2 : (0 : ℝ) < (K : ℝ) := lt_trans h1 hK
      exact_mod_cast h2
    refine ⟨K, hKpos, ?_⟩
    rw [div_le_iff₀ (by exact_mod_cast hKpos)]
    rw [div_lt_iff₀ hηpos] at hK
    linarith
  obtain ⟨K, hKpos, hKmesh⟩ := hex
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  set mesh : ℝ := (b - a) / K with hmesh
  have hmeshpos : 0 < mesh := by rw [hmesh]; exact div_pos (by linarith) hKposR
  have hmeshδ : mesh ≤ δ / 2 := (le_min_iff.mp hKmesh).1
  have hmesha : mesh ≤ ε * a / (100 * C * (L + 1)) := (le_min_iff.mp hKmesh).2
  have hKmeshR : (K : ℝ) * mesh = b - a := by
    rw [hmesh]; field_simp
  -- the grid
  set r : ℕ → ℝ := fun i => a + (i : ℝ) * mesh with hr
  have hr0 : r 0 = a := by simp [hr]
  have hrK : r K = b := by
    simp only [hr]
    rw [hKmeshR]
    ring
  have hrmono : ∀ i, r i ≤ r (i + 1) := by
    intro i
    simp only [hr]
    push_cast
    nlinarith [hmeshpos]
  have hrle : ∀ i ≤ K, r i ≤ b := by
    intro i hi
    have h1 : (i : ℝ) * mesh ≤ (K : ℝ) * mesh := by
      apply mul_le_mul_of_nonneg_right _ hmeshpos.le
      exact_mod_cast hi
    simp only [hr]
    linarith [hKmeshR]
  have hrge : ∀ i, a ≤ r i := by
    intro i
    simp only [hr]
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith [hmeshpos]
  -- the mass accuracy
  set em : ℝ := min (ε / (100 * C * ((K : ℝ) + 1))) 1 with hem
  have hempos : 0 < em := by rw [hem]; exact lt_min (by positivity) one_pos
  have hemle : em ≤ ε / (100 * C * ((K : ℝ) + 1)) := by
    rw [hem]; exact min_le_left _ _
  have hemlt : em ≤ 1 := by rw [hem]; exact min_le_right _ _
  have hgrid : ∀ᶠ N : ℕ in atTop, ∀ i ∈ Finset.range (K + 1),
      |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (Real.log (r i) - Real.log a)| ≤ em := by
    refine eventually_forall_finset _ _ ?_
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      refine Eventually.of_forall fun N => ?_
      have h0 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r 0)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = 0 := by
        simp [hr0]
      rw [h0, hr0]
      simp only [sub_self, abs_zero]
      exact hempos.le
    · have hai : a < r i := by
        have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hipos
        simp only [hr]
        nlinarith [hmeshpos]
      have ht := CumMass_tendsto a ha hai
      rw [Metric.tendsto_atTop] at ht
      obtain ⟨N0, hN0⟩ := ht em hempos
      filter_upwards [eventually_ge_atTop N0] with N hN
      have h1 := hN0 N hN
      rw [Real.dist_eq] at h1
      exact h1.le
  filter_upwards [hgrid, eventually_ge_atTop 3] with N hgN hN3
  intro β hβ y hy
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  set m : ℕ → ℕ := fun i => ⌊(N : ℝ) ^ (r i)⌋₊ with hm
  set xx : ℕ := ⌊(N : ℝ) ^ y⌋₊ with hxx
  set J : ℕ := ⌊(y - a) / mesh⌋₊ with hJ
  have hya : 0 ≤ y - a := by linarith [hy.1]
  have hJle : J ≤ K := by
    rw [hJ]
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ hmeshpos]
    have : y - a ≤ b - a := by linarith [hy.2]
    nlinarith [hKmeshR]
  have hrJ : r J ≤ y := by
    have h1 : ((J : ℕ) : ℝ) ≤ (y - a) / mesh := by
      rw [hJ]; exact Nat.floor_le (div_nonneg hya hmeshpos.le)
    have h2 : (J : ℝ) * mesh ≤ y - a := by
      have h3 := mul_le_mul_of_nonneg_right h1 hmeshpos.le
      have h4 : (y - a) / mesh * mesh = y - a := div_mul_cancel₀ _ hmeshpos.ne'
      linarith
    simp only [hr]
    linarith
  have hrsucc : y < r (J + 1) ∨ J = K := by
    rcases lt_or_ge J K with hJK | hKJ
    · left
      have h1 : (y - a) / mesh < (J : ℝ) + 1 := by
        rw [hJ]
        exact Nat.lt_floor_add_one ((y - a) / mesh)
      have h2 : y - a < ((J : ℝ) + 1) * mesh := by
        rw [div_lt_iff₀ hmeshpos] at h1
        linarith
      simp only [hr]
      push_cast
      linarith
    · right; omega
  -- the chain decomposition
  set F : ℕ → ℝ := fun k =>
    if k.Prime ∧ k.Coprime N then h (Real.log k / Real.log N + β) / ((k : ℝ) - 1) else 0 with hF
  have hmono : ∀ i < J, m i ≤ m (i + 1) := by
    intro i hi
    simp only [hm]
    apply Nat.floor_mono
    exact (Real.rpow_le_rpow_left_iff hN1).mpr (hrmono i)
  set mid : ℕ → ℝ := fun i => r i + mesh / 2 with hmid
  have hmidi : ∀ i, mid i = r i + mesh / 2 := fun i => by rw [hmid]
  have hmval : ∀ i, m i = ⌊(N : ℝ) ^ (r i)⌋₊ := fun i => by rw [hm]
  have hm0 : m 0 = ⌊(N : ℝ) ^ a⌋₊ := by
    rw [hm]
    exact congrArg (fun t => ⌊(N : ℝ) ^ t⌋₊) hr0
  have mmono : ∀ i j : ℕ, i ≤ j → m i ≤ m j := by
    intro i j hij
    simp only [hm]
    apply Nat.floor_mono
    exact (Real.rpow_le_rpow_left_iff hN1).mpr ((monotone_nat_of_le_succ hrmono) hij)
  have hmem2g : ∀ i < J, mid i + β ∈ Set.Icc (a / 2) (3 * b) := by
    intro i hi
    have hmeshle_b : mesh ≤ b := by
      have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
      have h2 : mesh ≤ (K : ℝ) * mesh := by nlinarith [hmeshpos]
      linarith [hKmeshR]
    have h1 : a ≤ mid i := by have := hmidi i; linarith [hrge i, hmeshpos]
    have h2 : mid i ≤ 2 * b := by have := hmidi i; have h3 := hrle i (by omega); linarith
    exact ⟨by linarith [hβ.1, ha, h1], by linarith [hβ.2, h2]⟩
  -- the integrand is continuous on `[a,b]`
  have hcontg : ContinuousOn (fun x : ℝ => h (x + β) / x) (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact hh.comp (continuousOn_id.add continuousOn_const) (fun x hx =>
        ⟨by linarith [hx.1, hβ.1, ha], by linarith [hx.2, hβ.2]⟩)
    · exact continuousOn_id
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hgint : ∀ p q : ℝ, a ≤ p → a ≤ q → p ≤ b → q ≤ b →
      IntervalIntegrable (fun x : ℝ => h (x + β) / x) volume p q := by
    intro p q hp hq hpb hqb
    apply ContinuousOn.intervalIntegrable
    refine hcontg.mono ?_
    intro x hx
    exact ⟨le_trans (le_min hp hq) hx.1, hx.2.trans (max_le hpb hqb)⟩
  -- the window sum is the chain sum
  have hsum_eq : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
        (fun p => p.Prime ∧ p.Coprime N),
        h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
      = ∑ k ∈ Finset.Ioc (m 0) xx, F k := by
    rw [← Finset.sum_filter]
    congr 1
    have hm0 : m 0 = ⌊(N : ℝ) ^ a⌋₊ := by
      rw [hm]
      exact congrArg (fun t => ⌊(N : ℝ) ^ t⌋₊) hr0
    rw [hxx, hm0]
  have hJx : m J ≤ xx := by
    simp only [hm, hxx]
    apply Nat.floor_mono
    exact (Real.rpow_le_rpow_left_iff hN1).mpr hrJ
  -- the integral splits along the same chain
  have hint_split : (∫ x in a..y, h (x + β) / x)
      = ∑ i ∈ Finset.range J, (∫ x in r i..r (i + 1), h (x + β) / x)
        + ∫ x in r J..y, h (x + β) / x := by
    have key : ∀ m : ℕ, m ≤ J →
        (∫ x in a..y, h (x + β) / x)
          = ∑ i ∈ Finset.range m, (∫ x in r i..r (i + 1), h (x + β) / x)
            + ∫ x in r m..y, h (x + β) / x := by
      intro m
      induction m with
      | zero => intro _; simp [hr0]
      | succ m ih =>
          intro hmJ
          rw [Finset.sum_range_succ, ih (by omega)]
          have hadd := intervalIntegral.integral_add_adjacent_intervals
            (hgint (r m) (r (m + 1)) (hrge m) (hrge _) (hrle m (by omega))
              (hrle (m + 1) (by omega)))
            (hgint (r (m + 1)) y (hrge _) hy.1 (hrle (m + 1) (by omega)) hy.2)
          rw [← hadd]
          ring
    exact key J le_rfl
  rw [hsum_eq, sum_Ioc_chain J hmono hJx, hint_split]
  -- per-band constants
  set mass : ℕ → ℝ := fun i => (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (i + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) with hmass
  set ld : ℕ → ℝ := fun i => Real.log (r (i + 1)) - Real.log (r i) with hld
  have hrin : ∀ i, r (i + 1) = r i + mesh := by
    intro i
    simp only [hr]
    push_cast
    ring
  -- per-band pointwise control of the sampled points
  have hstep : ∀ i < J, ∀ k ∈ Finset.Ioc (m i) (m (i + 1)), k.Prime → k.Coprime N →
      |h (Real.log k / Real.log N + β) - h (mid i + β)| ≤ eu := by
    intro i hi k hk hkp hkc
    obtain ⟨hkgt, hkle⟩ := Finset.mem_Ioc.mp hk
    have hik : (1 : ℝ) < (k : ℝ) := by
      have h2 : 2 ≤ k := hkp.two_le
      exact_mod_cast (show 1 < k by omega)
    have htk1 : r i < Real.log k / Real.log N := by
      rw [lt_div_iff₀ hlogN]
      have hk1 : (N : ℝ) ^ (r i) < (k : ℝ) := by
        have hm1 := hkgt
        rw [hmval i] at hm1
        have h3 : ((⌊(N : ℝ) ^ (r i)⌋₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
          exact_mod_cast (show ⌊(N : ℝ) ^ (r i)⌋₊ + 1 ≤ k by omega)
        have h4 : (N : ℝ) ^ (r i) < ((⌊(N : ℝ) ^ (r i)⌋₊ : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        linarith
      have h5 := Real.log_lt_log (Real.rpow_pos_of_pos hNpos (r i)) hk1
      rwa [Real.log_rpow hNpos] at h5
    have htk2 : Real.log k / Real.log N ≤ r (i + 1) := by
      rw [div_le_iff₀ hlogN]
      have hk2 : (k : ℝ) ≤ (N : ℝ) ^ (r (i + 1)) := by
        have hm2 := hkle
        rw [hmval (i + 1)] at hm2
        have h3 : (k : ℝ) ≤ ((⌊(N : ℝ) ^ (r (i + 1))⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm2
        have h4 : ((⌊(N : ℝ) ^ (r (i + 1))⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (r (i + 1)) :=
          Nat.floor_le (by positivity)
        linarith
      have h5 := Real.log_le_log (by positivity) hk2
      rwa [Real.log_rpow hNpos] at h5
    have htk3 : Real.log k / Real.log N ≤ b := htk2.trans (hrle (i + 1) (by omega))
    have hmem1 : Real.log k / Real.log N + β ∈ Set.Icc (a / 2) (3 * b) :=
      ⟨by linarith [htk1.le, hrge i, hβ.1, ha], by linarith [htk3, hβ.2]⟩
    have hmem2 : mid i + β ∈ Set.Icc (a / 2) (3 * b) := by
      have h1 : a ≤ mid i := by
        have := hmidi i; linarith [hrge i, hmeshpos]
      have hmeshle_b : mesh ≤ b := by
        have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
        have h2 : mesh ≤ (K : ℝ) * mesh := by nlinarith [hmeshpos]
        linarith [hKmeshR]
      have h2 : mid i ≤ 2 * b := by
        have := hmidi i; have h3 := hrle i (by omega); linarith
      exact ⟨by linarith [hβ.1, ha, h1], by linarith [hβ.2, h2]⟩
    have hdist : dist (Real.log k / Real.log N + β) (mid i + β) < δ := by
      rw [Real.dist_eq, show Real.log k / Real.log N + β - (mid i + β)
        = Real.log k / Real.log N - mid i from by ring, abs_lt]
      have h1 : Real.log k / Real.log N - mid i ≤ mesh / 2 := by
        have := hmidi i; have := hrin i; linarith [htk2]
      have h2 : -(mesh / 2) ≤ Real.log k / Real.log N - mid i := by
        have := hmidi i; have := hrin i; linarith [htk1]
      constructor
      · linarith [hmeshδ, hδpos]
      · linarith [hmeshδ, hδpos]
    have hres := hδ _ hmem1 _ hmem2 hdist
    rw [Real.dist_eq] at hres
    exact hres.le

  -- monotonicity of the cutoffs, and the band mass identity

  have hmasseq : ∀ i, mass i
      = ∑ k ∈ (Finset.Ioc (m i) (m (i + 1))).filter (fun k => k.Prime ∧ k.Coprime N),
          (1 : ℝ) / ((k : ℝ) - 1) := by
    intro i
    have h1 : mass i = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ (m (i + 1))).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ (m i)).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
      simp only [hmass, CumMass_eq_CumInt]
      rw [← hmval i, ← hmval (i + 1)]
    rw [h1]
    refine CumInt_sub a N ?_ (mmono i (i + 1) (Nat.le_succ i))
    rw [← hm0]
    exact mmono 0 i (Nat.zero_le i)
  -- nonnegativity of the band masses
  have hnonneg_w : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmasseq i]
    exact Finset.sum_nonneg fun k hk => by
      obtain ⟨-, hkp, -⟩ := Finset.mem_filter.mp hk
      have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkp.two_le
      have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      positivity
  -- the per-band bound
  have hband : ∀ i < J,
      |(∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
        - ∫ x in r i..r (i + 1), h (x + β) / x|
      ≤ eu * mass i + 2 * C * em + eu * ld i := by
    intro i hi
    set S := (Finset.Ioc (m i) (m (i + 1))).filter (fun k => k.Prime ∧ k.Coprime N) with hS
    set c := h (mid i + β) with hc
    -- the sum equals the weighted sum over `S`
    have hBeq : (∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
        = ∑ k ∈ S, h (Real.log k / Real.log N + β) / ((k : ℝ) - 1) := by
      rw [← Finset.sum_filter]
    -- the mass of `S` is `mass i`
    have hS1 : ∑ k ∈ S, (1 : ℝ) / ((k : ℝ) - 1) = mass i := (hmasseq i).symm
    -- the step error
    have hstep1 : |(∑ k ∈ S, h (Real.log k / Real.log N + β) * (1 / ((k : ℝ) - 1)))
        - c * mass i| ≤ eu * mass i := by
      rw [← hS1]
      refine abs_sum_mul_sub_const_mul_le S _ _ (fun k hk => ?_) (fun k hk => ?_)
      · obtain ⟨-, hkp, -⟩ := Finset.mem_filter.mp hk
        have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkp.two_le
        have : (0 : ℝ) < (k : ℝ) - 1 := by linarith
        positivity
      · obtain ⟨hkI, hkp, hkc⟩ := Finset.mem_filter.mp hk
        exact hstep i hi k hkI hkp hkc
    have hBeq2 : (∑ k ∈ S, h (Real.log k / Real.log N + β) * (1 / ((k : ℝ) - 1)))
        = ∑ k ∈ S, h (Real.log k / Real.log N + β) / ((k : ℝ) - 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      ring
    -- the weight `c` is bounded
    have hcC : |c| ≤ C := by
      rw [hc]
      refine habsC _ ⟨?_, ?_⟩
      · have h1 : a ≤ mid i := by have := hmidi i; linarith [hrge i, hmeshpos]
        linarith [hβ.1, ha]
      · have hmeshle_b : mesh ≤ b := by
          have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpos
          have h2 : mesh ≤ (K : ℝ) * mesh := by nlinarith [hmeshpos]
          linarith [hKmeshR]
        have h2 : mid i ≤ 2 * b := by
          have := hmidi i; have h3 := hrle i (by omega); linarith
        linarith [hβ.2]
    -- the logarithmic length of the band
    have hld2 : |mass i - ld i| ≤ 2 * em := by
      have h1 : |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (i + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (Real.log (r (i + 1)) - Real.log a)| ≤ em :=
        hgN (i + 1) (Finset.mem_range.mpr (by omega))
      have h2 : |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (Real.log (r i) - Real.log a)| ≤ em :=
        hgN i (Finset.mem_range.mpr (by omega))
      rw [hmass, hld]
      have : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (i + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))
          - (Real.log (r (i + 1)) - Real.log (r i))
          = ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (i + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (Real.log (r (i + 1)) - Real.log a))
            - ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (Real.log (r i) - Real.log a)) := by ring
      rw [this]
      exact (abs_sub _ _).trans (by linarith)
    -- the remaining comparison with the integral
    have hint1 : |c * ld i - ∫ x in r i..r (i + 1), h (x + β) / x| ≤ eu * ld i := by
      have hci : ContinuousOn (fun x => h (x + β)) (Set.Icc (r i) (r (i + 1))) := by
        refine hh.comp (continuousOn_id.add continuousOn_const) ?_
        intro x hx
        refine ⟨?_, ?_⟩
        · have : a ≤ r i := hrge i
          linarith [hx.1, hβ.1, ha]
        · have h2 : r (i + 1) ≤ b := hrle (i + 1) (by omega)
          linarith [hx.2, hβ.2]
      have hbound : ∀ x ∈ Set.Icc (r i) (r (i + 1)), |h (x + β) - c| ≤ eu := by
        intro x hx
        have hxmid : |x - mid i| ≤ mesh / 2 := by
          have e1 : mid i = r i + mesh / 2 := hmidi i
          have e2 : r (i + 1) = r i + mesh := hrin i
          have h1 : r i ≤ x := hx.1
          have h2 : x ≤ r (i + 1) := hx.2
          rw [abs_le]
          constructor <;> linarith
        have hmem : x + β ∈ Set.Icc (a / 2) (3 * b) := by
          refine ⟨?_, ?_⟩
          · have : a ≤ r i := hrge i
            linarith [hx.1, hβ.1, ha]
          · have h2 : r (i + 1) ≤ b := hrle (i + 1) (by omega)
            linarith [hx.2, hβ.2]
        have hdist : dist (x + β) (mid i + β) < δ := by
          have hxmid' := hxmid
          rw [abs_le] at hxmid'
          rw [Real.dist_eq, show x + β - (mid i + β) = x - mid i from by ring, abs_lt]
          constructor <;> linarith [hmeshδ, hδpos]
        have hres := hδ _ hmem _ (hmem2g i hi) hdist
        rw [Real.dist_eq] at hres
        rw [hc]
        exact hres.le
      have h := abs_integral_div_sub_const_le (a := r i) (b := r (i + 1))
        (lt_of_lt_of_le ha (hrge i)) (hrmono i) hci hbound
      rw [hld, abs_sub_comm]
      exact h
    have hC1 : |c * mass i - c * ld i| ≤ C * (2 * em) := by
      rw [show c * mass i - c * ld i = c * (mass i - ld i) by ring, abs_mul]
      exact mul_le_mul hcC hld2 (by positivity) (le_trans (abs_nonneg c) hcC)
    calc |(∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k) - ∫ x in r i..r (i + 1), h (x + β) / x|
        = |(∑ k ∈ S, h (Real.log k / Real.log N + β) * (1 / ((k : ℝ) - 1)))
            - ∫ x in r i..r (i + 1), h (x + β) / x| := by rw [hBeq, hBeq2]
      _ = |((∑ k ∈ S, h (Real.log k / Real.log N + β) * (1 / ((k : ℝ) - 1))) - c * mass i)
            + (c * mass i - c * ld i)
            + (c * ld i - ∫ x in r i..r (i + 1), h (x + β) / x)| := by
          congr 1
          ring
      _ ≤ eu * mass i + C * (2 * em) + eu * ld i := by
          refine (abs_add_three ..).trans ?_
          linarith [hstep1, hC1, hint1]
      _ = eu * mass i + 2 * C * em + eu * ld i := by ring_nf
  -- ===================== assembly =====================
  set Bt : ℝ := ∑ k ∈ Finset.Ioc (m J) xx, F k with hBt
  set It : ℝ := ∫ x in r J..y, h (x + β) / x with hIt
  -- telescoping of the band masses and of the logarithmic lengths
  have hmass0 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r 0)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = 0 := by simp [hr0]
  have hmasstel : ∑ i ∈ Finset.range J, mass i = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
    have hsum := Finset.sum_range_sub (fun i => (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r i)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) J
    have h2 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r 0)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
      rw [hmass0, sub_zero]
    rw [h2, ← hsum]
  have hldtel : ∑ i ∈ Finset.range J, ld i = Real.log (r J) - Real.log a := by
    have hsum := Finset.sum_range_sub (fun i => Real.log (r i)) J
    have h2 : Real.log (r J) - Real.log a = Real.log (r J) - Real.log (r 0) := by rw [hr0]
    rw [h2, ← hsum]
  have hJr : J ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
  have hgrJ := hgN J hJr
  have hlogrJ : Real.log (r J) - Real.log a ≤ L := by
    rw [hL]
    exact sub_le_sub_right (Real.log_le_log (by linarith [hrge J, ha]) (hrle J hJle)) _
  have hmassbd : ∑ i ∈ Finset.range J, mass i ≤ L + em := by
    rw [hmasstel]
    linarith [(abs_le.mp hgrJ).2]
  have hldbd : ∑ i ∈ Finset.range J, ld i ≤ L := by
    rw [hldtel]; exact hlogrJ
  -- the band part
  have hsum_band : ∑ i ∈ Finset.range J,
      |(∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
        - ∫ x in r i..r (i + 1), h (x + β) / x|
      ≤ eu * (∑ i ∈ Finset.range J, mass i) + 2 * C * em * (J : ℝ)
        + eu * (∑ i ∈ Finset.range J, ld i) := by
    refine (Finset.sum_le_sum fun i hi => hband i (Finset.mem_range.mp hi)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    linarith
  have hA : |∑ i ∈ Finset.range J,
      ((∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
        - ∫ x in r i..r (i + 1), h (x + β) / x)|
      ≤ eu * (L + em) + 2 * C * em * (J : ℝ) + eu * L := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (hsum_band.trans ?_)
    have h1 : eu * (∑ i ∈ Finset.range J, mass i) ≤ eu * (L + em) :=
      mul_le_mul_of_nonneg_left hmassbd heupos.le
    have h2 : eu * (∑ i ∈ Finset.range J, ld i) ≤ eu * L :=
      mul_le_mul_of_nonneg_left hldbd heupos.le
    linarith
  have hA1 : eu * (L + em) ≤ ε / 100 := by
    have hLem : L + em ≤ L + 1 := by linarith
    have h := mul_le_mul_of_nonneg_left hLem heupos.le
    linarith [heuL]
  have hA3 : eu * L ≤ ε / 100 := by
    have hL1 : L ≤ L + 1 := by linarith
    have h := mul_le_mul_of_nonneg_left hL1 heupos.le
    linarith [heuL]
  have hA2 : 2 * C * em * (J : ℝ) ≤ 2 * (ε / 100) := by
    have hJ1 : (J : ℝ) ≤ (K : ℝ) + 1 := by
      have h : (J : ℝ) ≤ (K : ℝ) := by exact_mod_cast hJle
      linarith
    have h2 : 2 * C * em * (J : ℝ) ≤ 2 * C * em * ((K : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hJ1 (by positivity)
    have hce : C * em ≤ C * (ε / (100 * C * ((K : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hemle hCpos.le
    have h2ce : 2 * (C * em) ≤ 2 * (C * (ε / (100 * C * ((K : ℝ) + 1)))) := by linarith
    have h3 : 2 * C * em * ((K : ℝ) + 1)
        ≤ 2 * C * (ε / (100 * C * ((K : ℝ) + 1))) * ((K : ℝ) + 1) := by
      have hk0 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
      have hstep := mul_le_mul_of_nonneg_right h2ce hk0
      calc 2 * C * em * ((K : ℝ) + 1) = 2 * (C * em) * ((K : ℝ) + 1) := by ring
        _ ≤ 2 * (C * (ε / (100 * C * ((K : ℝ) + 1)))) * ((K : ℝ) + 1) := hstep
        _ = 2 * C * (ε / (100 * C * ((K : ℝ) + 1))) * ((K : ℝ) + 1) := by ring
    have h4 : 2 * C * (ε / (100 * C * ((K : ℝ) + 1))) * ((K : ℝ) + 1)
        = 2 * (ε / 100) := by
      field_simp
    linarith
  have hCem : 2 * C * em ≤ 2 * (ε / 100) := by
    have hce : C * em ≤ C * (ε / (100 * C * ((K : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hemle hCpos.le
    have h2 : 2 * C * (ε / (100 * C * ((K : ℝ) + 1))) = 2 * ε / (100 * ((K : ℝ) + 1)) := by
      field_simp
    have h3 : 2 * ε / (100 * ((K : ℝ) + 1)) ≤ 2 * ε / 100 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      have hk0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith
    linarith
  -- the tail mass identity and the two tail bounds
  have hlogstep : Real.log (r (J + 1)) - Real.log (r J) ≤ mesh / a := by
    have hrJpos : (0 : ℝ) < r J := by linarith [hrge J, ha]
    have hrJ1pos : (0 : ℝ) < r (J + 1) := by linarith [hrge (J + 1), ha]
    have hratio : r (J + 1) / r J = 1 + mesh / r J := by
      rw [hrin J]; field_simp
    have hlog : Real.log (r (J + 1)) - Real.log (r J) = Real.log (r (J + 1) / r J) := by
      rw [Real.log_div hrJ1pos.ne' hrJpos.ne']
    rw [hlog, hratio]
    have h4 : Real.log (1 + mesh / r J) ≤ mesh / r J := by
      have hp : (0 : ℝ) < 1 + mesh / r J := by positivity
      have h := Real.log_le_sub_one_of_pos hp
      linarith
    have h5 : mesh / r J ≤ mesh / a := div_le_div_of_nonneg_left hmeshpos.le ha (hrge J)
    linarith
  have hTailmass : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) ≤ mesh / a + 2 * em := by
    rcases lt_or_ge J K with hJKlt | hKge
    · have hyJ : y < r (J + 1) := by
        rcases hrsucc with h | h
        · exact h
        · omega
      have hcum : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) ≤ (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (J + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) :=
        CumMass_mono a N (le_trans (by norm_num : (1 : ℕ) ≤ 3) hN3) (le_of_lt hyJ)
      have hg1 := hgN (J + 1) (Finset.mem_range.mpr (by omega))
      have h1 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r (J + 1))⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) ≤ Real.log (r (J + 1)) - Real.log a + em := by
        linarith [(abs_le.mp hg1).2]
      have h2 : Real.log (r J) - Real.log a - em ≤ (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
        linarith [(abs_le.mp hgrJ).1]
      linarith [hlogstep]
    · have hJK : J = K := le_antisymm hJle hKge
      have hle : y ≤ r J := by rw [hJK, hrK]; exact hy.2
      have hy_eq : y = r J := le_antisymm hle hrJ
      rw [hy_eq, sub_self]
      have hp1 : (0 : ℝ) < mesh / a := div_pos hmeshpos ha
      linarith only [hp1, hempos]
  have htailmass_eq : (∑ k ∈ (Finset.Ioc (m J) xx).filter (fun k => k.Prime ∧ k.Coprime N),
      (1 : ℝ) / ((k : ℝ) - 1)) = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by
    have h1 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ xx).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by rw [CumMass_eq_CumInt, ← hxx]
    have h2 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ (m J)).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) := by rw [CumMass_eq_CumInt, ← hmval]
    rw [h1, h2]
    refine (CumInt_sub a N (p := m J) (q := xx) ?_ ?_).symm
    · rw [← hm0]; exact mmono 0 J (Nat.zero_le J)
    · rw [hxx, hmval]
      exact Nat.floor_mono ((Real.rpow_le_rpow_left_iff hN1).mpr hrJ)
  have hlogk_lo : ∀ k ∈ Finset.Ioc (m J) xx, r J < Real.log k / Real.log N := by
    intro k hk
    obtain ⟨hkgt, -⟩ := Finset.mem_Ioc.mp hk
    rw [lt_div_iff₀ hlogN]
    have hk1 : (N : ℝ) ^ (r J) < (k : ℝ) := by
      have hmJ : m J = ⌊(N : ℝ) ^ (r J)⌋₊ := hmval J
      rw [hmJ] at hkgt
      have h3 : ((⌊(N : ℝ) ^ (r J)⌋₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast (show ⌊(N : ℝ) ^ (r J)⌋₊ + 1 ≤ k by omega)
      have h4 : (N : ℝ) ^ (r J) < ((⌊(N : ℝ) ^ (r J)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have h5 := Real.log_lt_log (Real.rpow_pos_of_pos hNpos (r J)) hk1
    rwa [Real.log_rpow hNpos] at h5
  have hlogk_hi : ∀ k ∈ Finset.Ioc (m J) xx, Real.log k / Real.log N ≤ y := by
    intro k hk
    obtain ⟨hk1, hkle⟩ := Finset.mem_Ioc.mp hk
    rw [div_le_iff₀ hlogN]
    have hk2 : (k : ℝ) ≤ (N : ℝ) ^ y := by
      have h4 : (k : ℝ) ≤ ((⌊(N : ℝ) ^ y⌋₊ : ℕ) : ℝ) := by
        rw [← hxx]; exact_mod_cast hkle
      have h5 : ((⌊(N : ℝ) ^ y⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ y := Nat.floor_le (by positivity)
      linarith
    have h6 := Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) hk2
    rwa [Real.log_rpow hNpos] at h6
  have hcCab : ∀ k ∈ Finset.Ioc (m J) xx, |h (Real.log k / Real.log N + β)| ≤ C := by
    intro k hk
    have hlow := hlogk_lo k hk
    have hhi := hlogk_hi k hk
    have hb0 : 0 < b := hb
    set s : ℝ := Real.log k / Real.log N with hs
    have hlow' : r J < s := hlow
    have hhi' : s ≤ y := hhi
    refine habsC (s + β) ⟨?_, ?_⟩
    · have h1 : a ≤ s := le_of_lt (lt_of_le_of_lt (hrge J) hlow')
      linarith only [h1, hβ.1, ha]
    · have h1 : s ≤ b := le_trans hhi' hy.2
      linarith only [h1, hβ.2, hb0]
  have hBtabs : |Bt| ≤ C * ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) := by
    have hBeq : Bt = ∑ k ∈ (Finset.Ioc (m J) xx).filter (fun k => k.Prime ∧ k.Coprime N),
        h (Real.log k / Real.log N + β) / ((k : ℝ) - 1) := by
      rw [hBt, hF, Finset.sum_filter]
    rw [hBeq, ← htailmass_eq, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    obtain ⟨hkI, hkp, hkc⟩ := Finset.mem_filter.mp hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkp.two_le
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    rw [abs_div, abs_of_pos hk1]
    calc |h (Real.log k / Real.log N + β)| / ((k : ℝ) - 1)
        ≤ C / ((k : ℝ) - 1) := div_le_div_of_nonneg_right (hcCab k hkI) hk1.le
      _ = C * (1 / ((k : ℝ) - 1)) := by ring
  have hItabs : |It| ≤ C * (Real.log y - Real.log (r J)) := by
    have hcont : ContinuousOn (fun x : ℝ => h (x + β)) (Set.Icc (r J) y) := by
      refine hh.comp (continuousOn_id.add continuousOn_const) ?_
      intro x hx
      exact ⟨by linarith [hx.1, hrge J, hβ.1, ha, hb], by linarith [hx.2, hy.2, hβ.2, hb]⟩
    have hbnd : ∀ x ∈ Set.Icc (r J) y, |h (x + β) - 0| ≤ C := by
      intro x hx
      have hx' : x + β ∈ Set.Icc (a / 2) (3 * b) :=
        ⟨by linarith [hx.1, hrge J, hβ.1, ha, hb], by linarith [hx.2, hy.2, hβ.2, hb]⟩
      have h2 := habsC _ hx'
      simpa only [sub_zero] using h2
    have hmain := abs_integral_div_sub_const_le (g := fun x : ℝ => h (x + β)) (c := 0) (C := C)
      (lt_of_lt_of_le ha (hrge J)) hrJ hcont hbnd
    simpa [hIt] using hmain
  have hlogtail : Real.log y - Real.log (r J) ≤ mesh / a := by
    rcases hrsucc with hyJ | hJK
    · have hypos : (0 : ℝ) < y := by linarith [hy.1, ha]
      have h1 : Real.log y ≤ Real.log (r (J + 1)) :=
        Real.log_le_log hypos (le_of_lt hyJ)
      linarith [hlogstep]
    · have hle : y ≤ r J := by rw [hJK, hrK]; exact hy.2
      have hy_eq : y = r J := le_antisymm hle hrJ
      rw [hy_eq, sub_self]
      exact div_nonneg hmeshpos.le ha.le
  have hCm : C * (mesh / a) ≤ ε / 100 := by
    have h1 : mesh / a ≤ ε / (100 * C * (L + 1)) := by
      calc mesh / a ≤ (ε * a / (100 * C * (L + 1))) / a :=
            div_le_div_of_nonneg_right hmesha ha.le
        _ = ε / (100 * C * (L + 1)) := by field_simp
    have h2 : C * (mesh / a) ≤ C * (ε / (100 * C * (L + 1))) :=
      mul_le_mul_of_nonneg_left h1 hCpos.le
    have h3 : C * (ε / (100 * C * (L + 1))) = ε / (100 * (L + 1)) := by
      field_simp
    have h4 : ε / (100 * (L + 1)) ≤ ε / 100 := by
      apply div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
    linarith
  have hBt2 : |Bt| ≤ ε / 100 + 2 * (ε / 100) := by
    have h1 : C * ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1)) - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ (r J)⌋₊).filter (fun p => p.Prime ∧ p.Coprime N), (1 : ℝ) / ((p : ℝ) - 1))) ≤ C * (mesh / a + 2 * em) :=
      mul_le_mul_of_nonneg_left hTailmass hCpos.le
    have h2 : C * (mesh / a + 2 * em) = C * (mesh / a) + 2 * C * em := by ring
    linarith [hBtabs, hCm, hCem]
  have hIt2 : |It| ≤ ε / 100 := by
    have h1 : C * (Real.log y - Real.log (r J)) ≤ C * (mesh / a) :=
      mul_le_mul_of_nonneg_left hlogtail hCpos.le
    linarith [hItabs, hCm]
  -- the two pieces against `ε`
  have hAbound : |∑ i ∈ Finset.range J,
      ((∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
        - ∫ x in r i..r (i + 1), h (x + β) / x)| ≤ 4 * (ε / 100) := by
    linarith [hA, hA1, hA2, hA3]
  have hgoal_eq : ((∑ i ∈ Finset.range J, ∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k) + Bt)
        - ((∑ i ∈ Finset.range J, ∫ x in r i..r (i + 1), h (x + β) / x) + It)
      = (∑ i ∈ Finset.range J,
          ((∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
            - ∫ x in r i..r (i + 1), h (x + β) / x)) + (Bt - It) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hgoal_eq]
  have htri : |(∑ i ∈ Finset.range J,
        ((∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
          - ∫ x in r i..r (i + 1), h (x + β) / x)) + (Bt - It)|
      ≤ |∑ i ∈ Finset.range J,
        ((∑ k ∈ Finset.Ioc (m i) (m (i + 1)), F k)
          - ∫ x in r i..r (i + 1), h (x + β) / x)| + |Bt - It| := abs_add_le _ _
  have htri2 : |Bt - It| ≤ |Bt| + |It| := abs_sub_le_abs_add Bt It
  have hle8 : 4 * (ε / 100) + (ε / 100 + 2 * (ε / 100)) + ε / 100 ≤ ε := by linarith
  linarith [htri, htri2, hAbound, hBt2, hIt2, hle8]

/-! ### The two-sided window form, in the two shapes the leaf needs -/

/-- `N ^ (log p / log N) = p` for `N > 1`, `p > 0`. -/
private lemma rpow_log_div_log {N : ℝ} (hN : 1 < N) {p : ℝ} (hp : 0 < p) :
    N ^ (Real.log p / Real.log N) = p := by
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hpos : (0 : ℝ) < N ^ (Real.log p / Real.log N) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine Real.log_injOn_pos (Set.mem_Ioi.2 hpos) (Set.mem_Ioi.2 hp) ?_
  rw [Real.log_rpow (by linarith)]
  field_simp

set_option maxHeartbeats 4000000 in
/-- Two-sided window form of `band_uniform_add`: the band mass over `N ^ z ≤ p ≤ N ^ y`
against the integral over `[z, y]`, uniform in the shift `β` and in both endpoints. -/
private lemma band_window (a b : ℝ) (ha : 0 < a) (hab : a < b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc (a / 2) (3 * b))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ β ∈ Set.Icc (-(a / 2)) b, ∀ z ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, z ≤ y →
      |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ z⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
            (fun p => p.Prime ∧ p.Coprime N),
          h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in z..y, h (xx + β) / xx| ≤ ε := by
  have h2ε : (0 : ℝ) < ε / 2 := by linarith
  have hband := band_uniform_add a b ha hab hh h2ε
  filter_upwards [hband, eventually_ge_atTop 3] with N hN hN3
  intro β hβ z hz y hy hzy
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmono : ∀ u v : ℝ, u ≤ v → ⌊(N : ℝ) ^ u⌋₊ ≤ ⌊(N : ℝ) ^ v⌋₊ := fun u v huv =>
    Nat.floor_mono ((Real.rpow_le_rpow_left_iff hN1).mpr huv)
  have haz : ⌊(N : ℝ) ^ a⌋₊ ≤ ⌊(N : ℝ) ^ z⌋₊ := hmono a z hz.1
  have hzy : ⌊(N : ℝ) ^ z⌋₊ ≤ ⌊(N : ℝ) ^ y⌋₊ := hmono z y hzy
  have h1 := hN β hβ y hy
  have h2 := hN β hβ z hz
  have hdisj : Disjoint ((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
        (fun p => p.Prime ∧ p.Coprime N))
      ((Finset.Ioc ⌊(N : ℝ) ^ z⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter (fun p => p.Prime ∧ p.Coprime N)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx hx'
    omega
  have hbig : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
        (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
      = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        + ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ z⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1) := by
    rw [← Finset.Ioc_union_Ioc_eq_Ioc haz hzy, Finset.filter_union, Finset.sum_union hdisj]
  have hsumz : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ z⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
        (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
      = (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1)) := by
    linarith [hbig]
  have hcont : ∀ p q : ℝ, a ≤ p → q ≤ b → p ≤ q →
      IntervalIntegrable (fun x : ℝ => h (x + β) / x) volume p q := by
    intro p q hp hqb hpq
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => ?_)
    · refine hh.comp (continuousOn_id.add continuousOn_const) ?_
      intro x hx
      exact ⟨by linarith [hx.1, hβ.1, ha], by linarith [hx.2, hqb, hβ.2]⟩
    · exact ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le ha hp) hx.1)
  have hint : (∫ xx in z..y, h (xx + β) / xx)
      = (∫ xx in a..y, h (xx + β) / xx) - (∫ xx in a..z, h (xx + β) / xx) := by
    have h1i := hcont a y le_rfl hy.2 hy.1
    have h2i := hcont a z le_rfl hz.2 hz.1
    exact (intervalIntegral.integral_interval_sub_left h1i h2i).symm
  rw [hsumz, hint]
  have heq : ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1)))
      - ((∫ xx in a..y, h (xx + β) / xx) - (∫ xx in a..z, h (xx + β) / xx))
      = ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..y, h (xx + β) / xx)
        - ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..z, h (xx + β) / xx) := by ring
  rw [heq]
  have ht2 : |((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..y, h (xx + β) / xx)
        - ((∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..z, h (xx + β) / xx)|
      ≤ |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ y⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..y, h (xx + β) / xx|
        + |(∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ z⌋₊).filter
          (fun p => p.Prime ∧ p.Coprime N), h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ xx in a..z, h (xx + β) / xx| :=
    abs_sub_le_abs_add _ _
  linarith [ht2, h1, h2]

set_option maxHeartbeats 4000000 in
/-- Window form with natural cutoffs: the mass of the primes in `Ioc m n` against the
integral from `log m / log N` to `log n / log N`. Both index sets of `lowerSum4` are exactly
of this shape — `Ioc (⌈N ^ κ1⌉ - 1) (⌈N ^ κ2⌉ - 1)` for the outer sum and `Ioc p (⌈N ^ κ2⌉ - 1)`
for the inner one — because `⌊N ^ (log m / log N)⌋ = m`. -/
private lemma band_window_cut (a b : ℝ) (ha : 0 < a) (hab : a < b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc (a / 4) (3 * b))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ β ∈ Set.Icc (-(a / 4)) b, ∀ m n : ℕ,
      ⌊(N : ℝ) ^ a⌋₊ - 1 ≤ m → m ≤ n → n ≤ ⌊(N : ℝ) ^ b⌋₊ →
      |(∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
          h (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..(Real.log n / Real.log N), h (x + β) / x| ≤ ε := by
  have hhalf : (0 : ℝ) < a / 2 := by linarith
  have hlt : a / 2 < b := by linarith
  have hband := band_window (a / 2) b hhalf hlt (hh := hh.mono (Set.Icc_subset_Icc
    (by linarith) le_rfl)) (ε := ε) hε
  have hbig : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  have hlogbig : ∀ᶠ N : ℕ in atTop, 2 * Real.log 2 / a ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * Real.log 2 / a))
  filter_upwards [hband, hbig, hlogbig, eventually_ge_atTop 3] with N hN hbigN hlogbigN hN3
  intro β hβ m n hm hmn hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hmlow : 4 ≤ ⌊(N : ℝ) ^ a⌋₊ := Nat.le_floor (by simpa using hbigN)
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := le_trans hm1 hmn
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmR : (N : ℝ) ^ a / 2 ≤ (m : ℝ) := by
    have h4 : 1 ≤ ⌊(N : ℝ) ^ a⌋₊ := by omega
    have hcast : ((⌊(N : ℝ) ^ a⌋₊ - 1 : ℕ) : ℝ)
        = ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub h4, Nat.cast_one]
    have h1 : ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) - 1 ≤ (m : ℝ) := by
      rw [← hcast]
      exact_mod_cast hm
    have h2 : (N : ℝ) ^ a - 2 ≤ ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) - 1 := by
      have h3 : (N : ℝ) ^ a - 1 < ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
      linarith only [h3]
    have h5 : (N : ℝ) ^ a / 2 ≤ (N : ℝ) ^ a - 2 := by linarith only [hbigN]
    exact h5.trans (h2.trans h1)
  have hlogm_lo : a * Real.log (N : ℝ) - Real.log 2 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) ^ a / 2) hmR
    rwa [Real.log_div (Real.rpow_pos_of_pos hNpos a).ne' (by norm_num),
      Real.log_rpow hNpos] at h
  have hn_hi : (n : ℝ) ≤ (N : ℝ) ^ b := by
    have h1 : ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ b := Nat.floor_le (by positivity)
    have h2 : (n : ℝ) ≤ ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hlogmn : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hmpos (by exact_mod_cast hmn)
  have hlogn_hi : Real.log (n : ℝ) ≤ b * Real.log (N : ℝ) := by
    have h := Real.log_le_log hnpos hn_hi
    rwa [Real.log_rpow hNpos] at h
  have hzge : a / 2 ≤ Real.log (m : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlogN]
    have h2 : 2 * Real.log 2 ≤ a * Real.log (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hlogbigN ha.le
      have h3 : a * (2 * Real.log 2 / a) = 2 * Real.log 2 := by
        field_simp
      linarith
    nlinarith [hlogm_lo, h2]
  have hzle : Real.log (m : ℝ) / Real.log (N : ℝ) ≤ b := by
    rw [div_le_iff₀ hlogN]
    have : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := hlogmn
    linarith
  have hzy : Real.log (m : ℝ) / Real.log (N : ℝ) ≤ Real.log (n : ℝ) / Real.log (N : ℝ) :=
    div_le_div_of_nonneg_right hlogmn hlogN.le
  have hf_lo : a / 2 ≤ Real.log (n : ℝ) / Real.log (N : ℝ) := le_trans hzge hzy
  have hf_hi : Real.log (n : ℝ) / Real.log (N : ℝ) ≤ b := by
    rw [div_le_iff₀ hlogN]
    have h1 : Real.log (n : ℝ) ≤ b * Real.log (N : ℝ) := hlogn_hi
    linarith
  have hfm : ⌊(N : ℝ) ^ (Real.log (m : ℝ) / Real.log (N : ℝ))⌋₊ = m := by
    rw [rpow_log_div_log hN1 hmpos, Nat.floor_natCast]
  have hfn : ⌊(N : ℝ) ^ (Real.log (n : ℝ) / Real.log (N : ℝ))⌋₊ = n := by
    rw [rpow_log_div_log hN1 hnpos, Nat.floor_natCast]
  have hres := hN β (⟨by linarith [hβ.1], hβ.2⟩)
    (Real.log (m : ℝ) / Real.log (N : ℝ)) ⟨hzge, hzle⟩
    (Real.log (n : ℝ) / Real.log (N : ℝ)) ⟨hf_lo, hf_hi⟩ hzy
  rwa [hfm, hfn] at hres

/-! ### The exact iterated form of `lowerSum4` -/

/-- `⌈N ^ κ2⌉ ≤ N`, so the top cutoff is below `N`. -/
private lemma ceil_rpow_kappa2_le_self {N : ℕ} (hN : 1 ≤ N) :
    ⌈(N : ℝ) ^ kappa2⌉₊ ≤ N := by
  have h1 : (N : ℝ) ^ kappa2 ≤ (N : ℝ) := by
    rcases lt_or_eq_of_le hN with h | h
    · calc (N : ℝ) ^ kappa2 ≤ (N : ℝ) ^ (1 : ℝ) :=
            (Real.rpow_le_rpow_left_iff (by exact_mod_cast h : (1 : ℝ) < N)).mpr
              (by norm_num [kappa2])
        _ = (N : ℝ) := Real.rpow_one _
    · rw [← h]; simp
  exact Nat.ceil_le.mpr h1

/-- For naturals and `x > 0`, `p < x` is `p ≤ ⌈x⌉ - 1`. -/
private lemma lt_iff_le_ceil_sub_one {x : ℝ} (hx : 0 < x) {p : ℕ} :
    (p : ℝ) < x ↔ p ≤ ⌈x⌉₊ - 1 := by
  have hpos : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  rw [← Nat.lt_ceil (a := x) (n := p)]
  omega

set_option maxHeartbeats 2000000 in
/-- `lowerSum4` written as an iterated sum over the two natural cutoffs
`⌈N ^ κ1⌉ - 1` and `⌈N ^ κ2⌉ - 1`, which are exactly the conditions `N ^ κ1 ≤ p` and
`p < N ^ κ2`. The identity is exact, with no boundary term. -/
private lemma lowerSum4_iterate {N : ℕ} (hN : 2 ≤ N) (B : ℝ) (f : ℝ → ℝ) :
    lowerSum4 f B N
      = ∑ p ∈ (Finset.Ioc (⌈(N : ℝ) ^ kappa1⌉₊ - 1) (⌈(N : ℝ) ^ kappa2⌉₊ - 1)).filter
            (fun p => p.Prime ∧ p.Coprime N),
          (1 : ℝ) / ((p : ℝ) - 1) *
            ∑ q ∈ (Finset.Ioc p (⌈(N : ℝ) ^ kappa2⌉₊ - 1)).filter
              (fun q => q.Prime ∧ q.Coprime N),
              f (lowerLevel B N (p * q)) / ((q : ℝ) - 1) := by
  have hNm : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have Nr : (0 : ℝ) < (N : ℝ) := by linarith
  have hx2 : (0 : ℝ) < (N : ℝ) ^ kappa2 := Real.rpow_pos_of_pos Nr _
  have hx1 : (0 : ℝ) < (N : ℝ) ^ kappa1 := Real.rpow_pos_of_pos Nr _
  set n : ℕ := ⌈(N : ℝ) ^ kappa2⌉₊ - 1 with hn
  have hnlt : n < N := by
    have h : ⌈(N : ℝ) ^ kappa2⌉₊ ≤ N := ceil_rpow_kappa2_le_self (by omega)
    have h2 : 0 < ⌈(N : ℝ) ^ kappa2⌉₊ := Nat.ceil_pos.mpr hx2
    omega
  set m : ℕ := ⌈(N : ℝ) ^ kappa1⌉₊ - 1 with hm
  have hSp : (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N)
      = (Finset.range N).filter (fun p => m < p ∧ p ≤ n ∧ p.Prime ∧ p.Coprime N) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h1, h2, h3, h4⟩
    · rintro ⟨-, h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  have hTp : ∀ p : ℕ, (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N)
      = (Finset.range N).filter (fun q => p < q ∧ q ≤ n ∧ q.Prime ∧ q.Coprime N) := by
    intro p
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by omega, h1, h2, h3, h4⟩
    · rintro ⟨-, h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [lowerSum4, lowerPairs4, Wu08Sum.P2, Finset.sum_filter, Finset.sum_product, hSp,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hTp p, Finset.sum_filter]
  by_cases hA : m < p ∧ p ≤ n ∧ p.Prime ∧ p.Coprime N
  · rw [if_pos hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hB : p < q ∧ q ≤ n ∧ q.Prime ∧ q.Coprime N
    · have hp_ge : (N : ℝ) ^ kappa1 ≤ (p : ℝ) := by
        have hm' : ⌈(N : ℝ) ^ kappa1⌉₊ - 1 < p := hA.1
        have hc : ⌈(N : ℝ) ^ kappa1⌉₊ ≤ p := by omega
        exact Nat.ceil_le.mp hc
      have hq_lt : (q : ℝ) < (N : ℝ) ^ kappa2 := by
        rw [lt_iff_le_ceil_sub_one hx2]
        exact hB.2.1
      have hψ : p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
          ((N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2) :=
        ⟨hA.2.2.1, hB.2.2.1, hA.2.2.2, hB.2.2.2, hp_ge, hB.1, hq_lt⟩
      rw [if_pos hB, if_pos hψ, totient_mul_of_lt hA.2.2.1 hB.2.2.1 hB.1, Nat.cast_mul]
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
      have hq1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one]
      rw [hp1, hq1]
      field_simp
    · have hψn : ¬(p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
          ((N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2)) := by
        rintro ⟨-, hqp, -, hqc, -, hpq, hlt⟩
        exact hB ⟨hpq, by rw [lt_iff_le_ceil_sub_one hx2] at hlt; exact hlt, hqp, hqc⟩
      rw [if_neg hB, if_neg hψn, mul_zero]
  · have hψn : ∀ q : ℕ, ¬(p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
        ((N : ℝ) ^ kappa1 ≤ (p : ℝ) ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2)) := by
      intro q hψ
      apply hA
      refine ⟨?_, ?_, hψ.1, hψ.2.2.1⟩
      · have hpos : 1 ≤ ⌈(N : ℝ) ^ kappa1⌉₊ := Nat.ceil_pos.mpr hx1
        have hc : ⌈(N : ℝ) ^ kappa1⌉₊ ≤ p := Nat.ceil_le.mpr hψ.2.2.2.2.1
        have hm' : ⌈(N : ℝ) ^ kappa1⌉₊ - 1 < p := by omega
        exact hm'
      · have hlt := hψ.2.2.2.2.2.2
        have hqle : q ≤ n := by
          rw [hn]
          exact (lt_iff_le_ceil_sub_one hx2).mp hlt
        have hpq := hψ.2.2.2.2.2.1
        exact le_trans (le_of_lt hpq) hqle
    rw [if_neg hA]
    exact Finset.sum_eq_zero fun q _ => by rw [if_neg (hψn q)]

/-! ### Continuity of the window integral -/

set_option maxHeartbeats 2000000 in
/-- The window integral `x ↦ ∫_u x..b, Φ (x + u) / u` is continuous on `[a/4, 3b]`.
Both the integrand and the endpoint are clamped in a way that does not change the integral,
so the parametric-integral lemma applies. -/
private lemma continuousOn_windowIntegral {Φ : ℝ → ℝ} {a b : ℝ}
    (hΦ : ContinuousOn Φ (Set.Icc (a / 2) (8 * b))) (ha : 0 < a) (hb : a / 8 ≤ b)
    (hb4 : a / 4 ≤ b) :
    ContinuousOn (fun x : ℝ => ∫ u in x..b, Φ (x + u) / u) (Set.Icc (a / 4) (3 * b)) := by
  set P : ℝ → ℝ := fun s => Φ (max (a / 2) (min (8 * b) s)) with hP
  have hPc : Continuous P :=
    hΦ.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
      fun s => ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  set Q : ℝ → ℝ := fun u => (max (a / 8) (min (4 * b) u))⁻¹ with hQ
  have hQden : ∀ u : ℝ, max (a / 8) (min (4 * b) u) ≠ 0 := by
    intro u h0
    have h1 : a / 8 ≤ max (a / 8) (min (4 * b) u) := le_max_left _ _
    rw [h0] at h1
    linarith
  have hQc : Continuous Q :=
    Continuous.inv₀ (continuous_const.max (continuous_const.min continuous_id)) hQden
  have hFc : Continuous (Function.uncurry (fun x u : ℝ => P (x + u) * Q u)) :=
    (hPc.comp (continuous_fst.add continuous_snd)).mul (hQc.comp continuous_snd)
  have hcont : Continuous fun x : ℝ => -(∫ u in b..x, P (x + u) * Q u) := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := b) hFc continuous_id
    exact this.neg
  refine hcont.continuousOn.congr ?_
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hcongr : (∫ u in b..x, Φ (x + u) / u) = ∫ u in b..x, P (x + u) * Q u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hsub : Set.uIcc b x ⊆ Set.Icc (a / 4) (3 * b) :=
      Set.uIcc_subset_Icc ⟨hb4, by linarith only [ha, hb4]⟩ ⟨hx1, hx2⟩
    obtain ⟨hu3, hu4⟩ := hsub hu
    have h1b : x + u ≤ 8 * b := by linarith only [hx2, hu4, ha, hb4]
    have h1 : max (a / 2) (min (8 * b) (x + u)) = x + u := by
      rw [min_eq_right h1b, max_eq_right (by linarith only [hx1, hu3, ha])]
    have h2b : u ≤ 4 * b := by linarith only [hu4, ha, hb4]
    have h2 : max (a / 8) (min (4 * b) u) = u := by
      rw [min_eq_right h2b, max_eq_right (by linarith only [hu3, ha])]
    simp only [hP, hQ]
    rw [h1, h2]
    simp only [div_eq_mul_inv]
  have hsym : (∫ u in x..b, Φ (x + u) / u) = -∫ u in b..x, Φ (x + u) / u := by
    have hs := intervalIntegral.integral_symm (μ := volume) (a := x) (b := b)
      (f := fun u : ℝ => Φ (x + u) / u)
    linarith [hs]
  show (∫ u in x..b, Φ (x + u) / u) = -(∫ u in b..x, P (x + u) * Q u)
  rw [hsym, hcongr]

/-! ### The level of a pair, and the shift to `Phi` -/

set_option maxHeartbeats 1000000 in
/-- The level of a prime pair, in terms of `t_p = log p / log N` and `t_q`: the only
difference from `(1/2 - t_p - t_q) / κ1` is the vanishing shift `12 B loglog N / log N`. -/
private lemma lowerLevel_pair {N : ℕ} (hN : 3 ≤ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (B : ℝ) :
    lowerLevel B N (p * q)
      = ((1 / 2 : ℝ) - Real.log (p : ℝ) / Real.log (N : ℝ)
          - Real.log (q : ℝ) / Real.log (N : ℝ)) / kappa1
        - 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hnumpos : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log (N : ℝ)) ^ B :=
    div_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hlogN B)
  have hcast : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by rw [Nat.cast_mul]; positivity
  have hden : Real.log ((N : ℝ) ^ kappa1) = Real.log (N : ℝ) / 12 := by
    rw [Real.log_rpow hNpos]
    simp only [kappa1]
    ring
  unfold lowerLevel
  rw [Real.log_div hnumpos.ne' hcast.ne',
    Real.log_div (Real.rpow_pos_of_pos hNpos _).ne' (Real.rpow_pos_of_pos hlogN B).ne',
    Real.log_rpow hNpos, Real.log_rpow hlogN, hden, Nat.cast_mul,
    Real.log_mul hp0.ne' hq0.ne']
  simp only [kappa1]
  have h1 : Real.log (N : ℝ) ≠ 0 := hlogN.ne'
  have h2 : Real.log (N : ℝ) / 12 ≠ 0 := by positivity
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- The pair level is a shift of the `Phi`-argument, uniformly over the pair band: for large
even `N`, `f (lowerLevel B N (p*q))` is within `ε` of `f ((1/2 - t_p - t_q)/κ1)`. -/
private lemma phi_shift (F f : ℝ → ℝ) (h : Wu04Functional.IsLinearSieve F f) (B : ℝ)
    (hB : 0 < B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (N : ℝ) ^ kappa1 ≤ (p : ℝ) → (q : ℝ) < (N : ℝ) ^ kappa2 →
      |f (lowerLevel B N (p * q))
        - f ((1 / 2 - (Real.log (p : ℝ) / Real.log (N : ℝ)
            + Real.log (q : ℝ) / Real.log (N : ℝ))) / kappa1)| ≤ ε := by
  have hcont : ContinuousOn f (Set.Icc (1 : ℝ) 6) :=
    h.2.1.mono fun x hx => by
      have h1 : (0 : ℝ) < x := by linarith [hx.1]
      exact h1
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  have hsmall0 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h1.comp hlog
  have hsmall : Tendsto
      (fun N : ℕ => 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h2 := hsmall0.const_mul (12 * B)
    simpa [mul_assoc] using h2
  have hev : ∀ᶠ N : ℕ in atTop,
      12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ min (δ / 2) 1 :=
    hsmall.eventually (eventually_le_nhds (lt_min (by linarith) one_pos))
  obtain ⟨NW, hNW⟩ := eventually_atTop.1 hev
  obtain ⟨NL, hNL⟩ := lowerLevel_mem_window B hB
  filter_upwards [eventually_ge_atTop (max (max NW NL) 3)] with N hN
  intro p q hp hq hpq hpge hqle
  have hcδ : 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ min (δ / 2) 1 :=
    hNW N (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hwin := hNL N (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)) p q hpge hpq hqle
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlev := lowerLevel_pair hN3 hp hq B
  set c : ℝ := 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) with hc
  have hc0 : 0 ≤ c := by
    have hll : 0 ≤ Real.log (Real.log (N : ℝ)) := by
      apply Real.log_nonneg
      have h3 : (1 : ℝ) < Real.log 3 := by
        have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
        rwa [Real.log_exp] at h
      have h4 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      exact le_of_lt (h3.trans_le (Real.log_le_log (by norm_num) h4))
    have hdiv : 0 ≤ Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := div_nonneg hll hlogN.le
    have h12B : 0 ≤ 12 * B := by linarith
    rw [hc]
    exact mul_nonneg h12B hdiv
  have hc1 : c ≤ 1 := le_trans hcδ (min_le_right _ _)
  have hcδ2 : c ≤ δ / 2 := le_trans hcδ (min_le_left _ _)
  have hphieq : ((1 / 2 - (Real.log (p : ℝ) / Real.log (N : ℝ)
        + Real.log (q : ℝ) / Real.log (N : ℝ))) / kappa1)
      = lowerLevel B N (p * q) + c := by
    rw [hlev, hc]
    ring
  set lev : ℝ := lowerLevel B N (p * q) with hlevval
  have hlev2 : (2 : ℝ) ≤ lev := hwin.1
  have hlev5 : lev ≤ 5 := hwin.2
  have hlev1 : (1 : ℝ) ≤ lev := by linarith only [hlev2]
  have hphi1 : (1 : ℝ) ≤ lev + c := by linarith only [hlev2, hc0]
  have hphi6 : lev + c ≤ 6 := by linarith only [hlev5, hc1]
  have hdist : dist (lev + c) lev < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hc0]
    linarith only [hcδ2, hδpos]
  have hres := hδ (lev + c) ⟨hphi1, hphi6⟩ lev ⟨hlev1, by linarith only [hlev5]⟩ hdist
  rw [Real.dist_eq] at hres
  rw [hphieq]
  exact le_of_lt (by rwa [abs_sub_comm] at hres)

/-! ### The clamped window integral: continuity and identification -/

/-- `κ1 / 2 ≤ 1 / 4`: the lower clamp is below the upper one. -/
private lemma kappa1_half_le_quarter : kappa1 / 2 ≤ 1 / 4 := by norm_num [kappa1]

/-- The numerical bounds on `κ1`, `κ2` used by the clamped window. -/
private lemma kappa_bounds : kappa1 / 4 ≤ kappa2 ∧ kappa1 / 2 < kappa2 ∧ (2 : ℝ) * kappa2 ≤ 1 / 4 := by
  norm_num [kappa1, kappa2]

set_option maxHeartbeats 1000000 in
/-- Continuity of the clamped `Φ`. -/
private lemma clamped_phi_continuous {F f : ℝ → ℝ} (h : Wu04Functional.IsLinearSieve F f) :
    Continuous fun s : ℝ => f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) s)) / kappa1) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hg : Continuous fun s : ℝ => (1 / 2 - max (kappa1 / 2) (min (1 / 4) s)) / kappa1 := by
    fun_prop
  refine h.2.1.comp_continuous hg fun x => ?_
  have h1 : max (kappa1 / 2) (min (1 / 4) x) ≤ 1 / 4 :=
    max_le (by linarith [kappa1_half_le_quarter]) (min_le_left _ _)
  exact div_pos (by linarith) hk

set_option maxHeartbeats 2000000 in
/-- The clamped window integral is continuous on `[κ1/4, 3κ2]`. -/
private lemma clampedWindow_continuous {F f : ℝ → ℝ} (h : Wu04Functional.IsLinearSieve F f) :
    ContinuousOn (fun x : ℝ =>
      ∫ u in x..kappa2, f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) (x + u))) / kappa1) / u)
      (Set.Icc (kappa1 / 4) (3 * kappa2)) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hb4 : kappa1 / 4 ≤ kappa2 := kappa_bounds.1
  have hb : kappa1 / 8 ≤ kappa2 := by linarith [kappa_bounds.1]
  have hΦ : ContinuousOn (fun s : ℝ => f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) s)) / kappa1))
      (Set.Icc (kappa1 / 2) (8 * kappa2)) :=
    (clamped_phi_continuous h).continuousOn
  have hwin := continuousOn_windowIntegral (Φ := fun s : ℝ =>
      f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) s)) / kappa1)) hΦ hk hb (by linarith)
  simpa using hwin

set_option maxHeartbeats 2000000 in
/-- On the band `[κ1, κ2]` the inner clamp is the identity, so the clamped window integral is
the honest window integral. -/
private lemma clampedWindow_eq {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Icc kappa1 kappa2) :
    (∫ u in x..kappa2, f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) (x + u))) / kappa1) / u)
      = ∫ u in x..kappa2, f ((1 / 2 - (x + u)) / kappa1) / u := by
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk12 : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have hsub : Set.uIcc x kappa2 ⊆ Set.Icc kappa1 kappa2 :=
    Set.uIcc_subset_Icc ⟨hx.1, hx.2⟩ ⟨hk12, le_rfl⟩
  obtain ⟨hu1, hu2⟩ := hsub hu
  have h3 : kappa1 / 2 ≤ x + u := by linarith only [hx.1, hu1, hk]
  have h4 : x + u ≤ 1 / 4 := by linarith only [hx.2, hu2, kappa_bounds.2.2]
  congr 2
  rw [min_eq_right h4, max_eq_right h3]

set_option maxHeartbeats 2000000 in
/-- The unscaled `F4` double integral, with the inner integral in band form. -/
private lemma lowerIntegral4_eq {f : ℝ → ℝ} :
    lowerIntegral4 f
      = ∫ x in kappa1..kappa2, (∫ u in x..kappa2, f ((1 / 2 - (x + u)) / kappa1) / u) / x := by
  unfold lowerIntegral4
  refine intervalIntegral.integral_congr fun t ht => ?_
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  congr 2
  ring


/-! ### The total band weight and the band sum against the window integral -/

/-- `⌈x⌉ - 1 ≤ ⌊x⌋` for real `x`, in `ℕ`. -/
private lemma ceil_sub_one_le_floor {x : ℝ} : ⌈x⌉₊ - 1 ≤ ⌊x⌋₊ := by
  have h : ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 := Nat.ceil_le_floor_add_one x
  omega

/-- `log x - log b ≤ C / A` when `0 < A ≤ b < x` and `x - b ≤ C`. -/
private lemma log_sub_log_le_div {x b A C : ℝ} (hx : 0 < x) (hb : 0 < b) (hA : 0 < A)
    (hAb : A ≤ b) (hg : x - b ≤ C) (hC : 0 ≤ C) :
    Real.log x - Real.log b ≤ C / A := by
  have h1 : Real.log x - Real.log b = Real.log (x / b) :=
    (Real.log_div hx.ne' hb.ne').symm
  have h2 : Real.log (x / b) ≤ x / b - 1 := Real.log_le_sub_one_of_pos (div_pos hx hb)
  have h3 : x / b - 1 = (x - b) / b := by
    field_simp
  have h4 : (x - b) / b ≤ C / b := div_le_div_of_nonneg_right hg hb.le
  have h5 : C / b ≤ C / A := div_le_div_of_nonneg_left hC hA hAb
  linarith only [h1, h2, h3, h4, h5]

/-- `N ^ (2κ1/3) ≤ N ^ κ1 / 2` for `N ≥ 2^36`. -/
private lemma rpow_two_thirds {N : ℕ} (hN : 2 ^ 36 ≤ N) :
    (N : ℝ) ^ (2 * kappa1 / 3) ≤ (N : ℝ) ^ kappa1 / 2 := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by positivity
    exact_mod_cast this
  have hNpow : (2 : ℝ) ≤ (N : ℝ) ^ (kappa1 / 3) := by
    have h1 : ((2 : ℝ) ^ (36 : ℕ)) ^ (kappa1 / 3) ≤ (N : ℝ) ^ (kappa1 / 3) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num [kappa1])
    have h2 : ((2 : ℝ) ^ (36 : ℕ)) ^ (kappa1 / 3) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [kappa1]
    rwa [h2] at h1
  have h3 : (N : ℝ) ^ kappa1 = (N : ℝ) ^ (2 * kappa1 / 3) * (N : ℝ) ^ (kappa1 / 3) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  rw [h3]
  have h4 : (0 : ℝ) ≤ (N : ℝ) ^ (2 * kappa1 / 3) := Real.rpow_nonneg hNpos.le _
  linarith only [mul_le_mul_of_nonneg_left hNpow h4]

/-- The band `[N^κ1/2, N^κ2]` carries total weight at most `1` for large `N`. -/
private lemma band_weight_le_one :
    ∀ᶠ N : ℕ in atTop, ∀ m n : ℕ,
      (N : ℝ) ^ kappa1 / 2 ≤ (m : ℝ) → (n : ℝ) ≤ (N : ℝ) ^ kappa2 →
      (∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
          (1 : ℝ) / ((p : ℝ) - 1)) ≤ 1 := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hp0 : (0 : ℝ) < 2 * kappa1 / 3 := by norm_num [kappa1]
  have hp0k : 2 * kappa1 / 3 < kappa2 := by norm_num [kappa1, kappa2]
  have hk3 : (2 * kappa1 / 3 : ℝ) ≠ 0 := ne_of_gt hp0
  have hlim := band_prime_inv_pred_coprime (2 * kappa1 / 3) kappa2 hp0 hp0k
  have hlt : log kappa2 - log (2 * kappa1 / 3) < 1 := by
    have h1 : log kappa2 - log (2 * kappa1 / 3) = log (kappa2 / (2 * kappa1 / 3)) :=
      (Real.log_div (by norm_num [kappa2]) hk3).symm
    rw [h1]
    have h2 : kappa2 / (2 * kappa1 / 3) = 2 * (522 / 500) := by norm_num [kappa1, kappa2]
    rw [h2, Real.log_mul (by norm_num) (by norm_num)]
    have h3 : log (522 / 500 : ℝ) ≤ 522 / 500 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  have h1 := hlim.eventually (eventually_lt_nhds hlt)
  filter_upwards [h1, eventually_ge_atTop (2 ^ 36)] with N hN1 hN36
  intro m n hm hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by positivity
    exact_mod_cast this
  have hmn : ⌊(N : ℝ) ^ (2 * kappa1 / 3)⌋₊ ≤ m := by
    have h2 : (N : ℝ) ^ (2 * kappa1 / 3) ≤ (m : ℝ) :=
      le_trans (rpow_two_thirds hN36) hm
    have h3 : ((⌊(N : ℝ) ^ (2 * kappa1 / 3)⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) :=
      le_trans (Nat.floor_le (by positivity)) h2
    exact_mod_cast h3
  have hmn2 : n ≤ ⌊(N : ℝ) ^ kappa2⌋₊ := Nat.le_floor (by simpa using hn)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hN1.le
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · intro p hp hnp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have h4 : (2 : ℕ) ≤ p := hp.2.1.two_le
    have h5 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h4
    exact div_nonneg zero_le_one (by linarith)

set_option maxHeartbeats 2000000 in
/-- The inner window comparison: the band prime sum against `∫_{log m / log N}^{κ2}`,
uniform in the shift `β ∈ [0, κ2]` and in the lower cutoff. -/
private lemma band_limit_shift {k : ℝ → ℝ} {C : ℝ} (hCpos : 0 < C)
    (hk : ContinuousOn k (Set.Icc (kappa1 / 4) (3 * kappa2)))
    (hC : ∀ x ∈ Set.Icc (kappa1 / 4) (3 * kappa2), |k x| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ β ∈ Set.Icc 0 kappa2, ∀ m : ℕ,
      ⌊(N : ℝ) ^ kappa1⌋₊ - 1 ≤ m → m ≤ ⌈(N : ℝ) ^ kappa2⌉₊ - 1 →
      |(∑ p ∈ (Finset.Ioc m (⌈(N : ℝ) ^ kappa2⌉₊ - 1)).filter
            (fun p => p.Prime ∧ p.Coprime N),
          k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..kappa2, k (x + β) / x| ≤ ε := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk12 : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hkq : kappa1 / 4 ≤ kappa2 := kappa_bounds.1
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hwin := band_window_cut kappa1 kappa2 hk1 hk12 hk hε2
  have hbig : ∀ᶠ N : ℕ in atTop, 8 * C * Real.log 2 / (kappa1 * ε) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (8 * C * Real.log 2 / (kappa1 * ε)))
  have hbig2 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ kappa2 :=
    ((tendsto_rpow_atTop hk2).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  have hbig3 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ kappa1 :=
    ((tendsto_rpow_atTop hk1).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4)
  have hlim2 : Tendsto (fun N : ℕ => Real.log 2 / Real.log (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log 2 / x) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop tendsto_id
    exact h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hC4 : (0 : ℝ) < min (kappa1 / 4) (kappa2 - kappa1 / 4) :=
    lt_min (by linarith only [hk1]) (by linarith only [hk12, hk1])
  have hbig4 : ∀ᶠ N : ℕ in atTop,
      Real.log 2 / Real.log (N : ℝ) ≤ min (kappa1 / 4) (kappa2 - kappa1 / 4) :=
    (hlim2.eventually (eventually_lt_nhds hC4)).mono fun x hx => le_of_lt hx
  filter_upwards [hwin, hbig, hbig2, hbig3, hbig4, eventually_ge_atTop 4]
    with N hwinN hbigN hbig2N hbig3N hbig4N hN4
  intro β hβ m hm hmn
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hrpow1 : (0 : ℝ) < (N : ℝ) ^ kappa1 := Real.rpow_pos_of_pos hNpos _
  have hrpow2 : (0 : ℝ) < (N : ℝ) ^ kappa2 := Real.rpow_pos_of_pos hNpos _
  have hlog2q : Real.log 2 / Real.log (N : ℝ) ≤ kappa1 / 4 :=
    le_trans hbig4N (min_le_left _ _)
  have hlog2N : Real.log 2 / Real.log (N : ℝ) ≤ kappa1 / 2 :=
    le_trans hlog2q (by linarith only [hk1])
  have hlog2N' : Real.log 2 / Real.log (N : ℝ) ≤ kappa2 - kappa1 / 4 :=
    le_trans hbig4N (min_le_right _ _)
  set n : ℕ := ⌈(N : ℝ) ^ kappa2⌉₊ - 1 with hn
  have hceil2 : (1 : ℕ) ≤ ⌈(N : ℝ) ^ kappa2⌉₊ := Nat.ceil_pos.mpr hrpow2
  have hnR : ((⌈(N : ℝ) ^ kappa2⌉₊ - 1 : ℕ) : ℝ)
      = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hceil2, Nat.cast_one]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    have h5 : (N : ℝ) ^ kappa2 ≤ ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h6 : ((n : ℕ) : ℝ) = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := hn ▸ hnR
    linarith only [h5, h6, hbig2N]
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith only [hn2]
  have hnfl : n ≤ ⌊(N : ℝ) ^ kappa2⌋₊ := hn ▸ ceil_sub_one_le_floor
  -- the lower cutoff is at least `N ^ κ1 / 2`
  have hmR : (N : ℝ) ^ kappa1 / 2 ≤ (m : ℝ) := by
    have h1 : (1 : ℕ) ≤ ⌊(N : ℝ) ^ kappa1⌋₊ := Nat.le_floor (by
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ kappa1 := le_trans (by norm_num) hbig3N
      simpa using h2)
    have h2 : ((⌊(N : ℝ) ^ kappa1⌋₊ - 1 : ℕ) : ℝ)
        = ((⌊(N : ℝ) ^ kappa1⌋₊ : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
    have h3 : ((⌊(N : ℝ) ^ kappa1⌋₊ - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h4 : (N : ℝ) ^ kappa1 - 1 < ((⌊(N : ℝ) ^ kappa1⌋₊ : ℕ) : ℝ) := by
      have h5 := Nat.lt_floor_add_one ((N : ℝ) ^ kappa1)
      linarith only [h5]
    linarith only [h2, h3, h4, hbig3N]
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hmR
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith only [hmpos, hmR, hbig3N]
  have ha_pos : (0 : ℝ) < Real.log (m : ℝ) / Real.log N :=
    div_pos (Real.log_pos hm1) hlogN
  have ha_lo : kappa1 / 2 ≤ Real.log (m : ℝ) / Real.log N := by
    rw [le_div_iff₀ hlogN]
    have h1 : Real.log ((N : ℝ) ^ kappa1 / 2) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) hmR
    rw [Real.log_div hrpow1.ne' (by norm_num), Real.log_rpow hNpos] at h1
    have h3 : Real.log 2 ≤ (kappa1 / 2) * Real.log (N : ℝ) := by
      have h4 := mul_le_mul_of_nonneg_right hlog2N hlogN.le
      rwa [div_mul_cancel₀ _ hlogN.ne'] at h4
    have h5 : (kappa1 / 2) * Real.log (N : ℝ) ≤ kappa1 * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hk1]) hlogN.le
    linarith only [h1, h3, h5]
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hbn_lo : kappa1 / 4 ≤ Real.log (n : ℝ) / Real.log N := by
    rw [le_div_iff₀ hlogN]
    have h1 : Real.log ((N : ℝ) ^ kappa1 / 2) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (le_trans hmR hmnR)
    rw [Real.log_div hrpow1.ne' (by norm_num), Real.log_rpow hNpos] at h1
    have h3 : Real.log 2 ≤ (kappa1 / 4) * Real.log (N : ℝ) := by
      have h4 := mul_le_mul_of_nonneg_right hlog2q hlogN.le
      rwa [div_mul_cancel₀ _ hlogN.ne'] at h4
    have h5 : (kappa1 / 2) * Real.log (N : ℝ) ≤ kappa1 * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hk1]) hlogN.le
    have h6 : (kappa1 / 4) * Real.log (N : ℝ) + (kappa1 / 4) * Real.log (N : ℝ)
        = (kappa1 / 2) * Real.log (N : ℝ) := by ring
    linarith only [h1, h3, h5, h6]
  have hbn_hi : Real.log (n : ℝ) / Real.log N ≤ kappa2 := by
    have h2 : Real.log (n : ℝ) ≤ Real.log ((N : ℝ) ^ kappa2) := by
      refine Real.log_le_log hnpos ?_
      exact le_trans (by exact_mod_cast hnfl) (Nat.floor_le (by positivity))
    rw [Real.log_rpow hNpos] at h2
    exact (div_le_iff₀ hlogN).mpr h2
  have hgapn : kappa2 - Real.log (n : ℝ) / Real.log N ≤ Real.log 2 / Real.log N := by
    have h5 : (N : ℝ) ^ kappa2 / 2 ≤ (n : ℝ) := by
      have h6 : (N : ℝ) ^ kappa2 ≤ ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h7 : ((n : ℕ) : ℝ) = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := hn ▸ hnR
      linarith only [h6, h7, hbig2N]
    have h6 : Real.log ((N : ℝ) ^ kappa2 / 2) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h5
    have h6' : kappa2 * Real.log (N : ℝ) - Real.log 2 ≤ Real.log (n : ℝ) := by
      rw [Real.log_div hrpow2.ne' (by norm_num), Real.log_rpow hNpos] at h6
      linarith only [h6]
    have h8 : kappa2 - Real.log 2 / Real.log (N : ℝ) ≤ Real.log (n : ℝ) / Real.log N := by
      rw [le_div_iff₀ hlogN]
      have h9 : (kappa2 - Real.log 2 / Real.log (N : ℝ)) * Real.log (N : ℝ)
          = kappa2 * Real.log (N : ℝ) - Real.log 2 := by
        field_simp
      rw [h9]
      exact h6'
    linarith only [h8]
  -- the window comparison for the natural cutoffs
  have hW := hwinN β ⟨by linarith only [hβ.1, hk1], hβ.2⟩ m n hm hmn hnfl
  -- the upper endpoint correction
  have hn1 : (1 : ℝ) < (n : ℝ) := by linarith only [hnpos, hn2]
  have hbpos : (0 : ℝ) < Real.log (n : ℝ) / Real.log N :=
    div_pos (Real.log_pos hn1) hlogN
  have hcorr : |∫ x in (Real.log n / Real.log N)..kappa2, k (x + β) / x| ≤ ε / 2 := by
    have hcont : ContinuousOn (fun x : ℝ => k (x + β))
        (Set.Icc (Real.log (n : ℝ) / Real.log N) kappa2) := by
      refine hk.comp (continuousOn_id.add continuousOn_const) ?_
      intro x hx
      simp only [Pi.add_apply, id]
      exact ⟨by linarith only [hx.1, hbn_lo, hβ.1],
        by linarith only [hx.2, hβ.2, hk2]⟩
    have hb := abs_integral_div_sub_const_le (g := fun x : ℝ => k (x + β))
      (a := Real.log (n : ℝ) / Real.log N) (b := kappa2) (c := 0) (C := C)
      hbpos hbn_hi hcont
      (fun x hx => by
        have h1 : |k (x + β)| ≤ C := hC (x + β)
          ⟨by linarith only [hx.1, hbn_lo, hβ.1], by linarith only [hx.2, hβ.2, hk2]⟩
        simpa only [sub_zero] using h1)
    simp only [zero_mul, sub_zero] at hb
    have hstep : Real.log kappa2 - Real.log (Real.log (n : ℝ) / Real.log N)
        ≤ 4 * Real.log 2 / (kappa1 * Real.log N) := by
      have h1 : Real.log kappa2 - Real.log (Real.log (n : ℝ) / Real.log N)
          ≤ (Real.log 2 / Real.log N) / (kappa1 / 4) :=
        log_sub_log_le_div hk2 hbpos (by linarith only [hk1]) hbn_lo hgapn (by positivity)
      have h2 : (Real.log 2 / Real.log N) / (kappa1 / 4)
          = 4 * Real.log 2 / (kappa1 * Real.log N) := by
        field_simp
      linarith only [h1, h2]
    have harith : C * (4 * Real.log 2 / (kappa1 * Real.log N)) ≤ ε / 2 := by
      have h1 : 8 * C * Real.log 2 ≤ kappa1 * ε * Real.log N := by
        have h2 := mul_le_mul_of_nonneg_right hbigN (le_of_lt (mul_pos hk1 hε))
        rwa [div_mul_cancel₀ (8 * C * Real.log 2) (ne_of_gt (mul_pos hk1 hε)),
          mul_comm (Real.log (N : ℝ))] at h2
      rw [← mul_div_assoc]
      rw [div_le_iff₀ (mul_pos hk1 hlogN)]
      nlinarith only [h1, hlogN, hk1, hε.le]
    linarith only [hb, mul_le_mul_of_nonneg_left hstep hCpos.le, harith]
  -- decompose the integral at `log n / log N`
  have hintb : IntervalIntegrable (fun x : ℝ => k (x + β) / x) volume
      (Real.log (m : ℝ) / Real.log N) (Real.log (n : ℝ) / Real.log N) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by
      rw [div_le_div_iff_of_pos_right hlogN]
      exact Real.log_le_log hmpos hmnR)]
    refine (hk.comp (continuousOn_id.add continuousOn_const) ?_).div continuousOn_id ?_
    · intro x hx
      simp only [Pi.add_apply, id]
      exact ⟨by linarith only [hx.1, ha_lo, hβ.1, hk1], by linarith only [hx.2, hbn_hi, hβ.2, hk2]⟩
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le ha_pos hx.1)
  have hintc : IntervalIntegrable (fun x : ℝ => k (x + β) / x) volume
      (Real.log (n : ℝ) / Real.log N) kappa2 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hbn_hi]
    refine (hk.comp (continuousOn_id.add continuousOn_const) ?_).div continuousOn_id ?_
    · intro x hx
      simp only [Pi.add_apply, id]
      exact ⟨by linarith only [hx.1, hbn_lo, hβ.1], by linarith only [hx.2, hβ.2, hk2]⟩
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le hbpos hx.1)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hintb hintc
  have htri : |(∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
      - ∫ x in (Real.log m / Real.log N)..kappa2, k (x + β) / x|
      ≤ |(∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..(Real.log n / Real.log N), k (x + β) / x|
      + |∫ x in (Real.log n / Real.log N)..kappa2, k (x + β) / x| := by
    have h1 : (∫ x in (Real.log m / Real.log N)..kappa2, k (x + β) / x)
        = (∫ x in (Real.log m / Real.log N)..(Real.log n / Real.log N), k (x + β) / x)
          + ∫ x in (Real.log n / Real.log N)..kappa2, k (x + β) / x := hsplit.symm
    have h2 := abs_add_le ((∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..(Real.log n / Real.log N), k (x + β) / x)
      (- ∫ x in (Real.log n / Real.log N)..kappa2, k (x + β) / x)
    have h3 : ((∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..(Real.log n / Real.log N), k (x + β) / x)
        + (- ∫ x in (Real.log n / Real.log N)..kappa2, k (x + β) / x)
        = (∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        k (Real.log p / Real.log N + β) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..kappa2, k (x + β) / x := by
      rw [h1]; ring
    rw [h3] at h2
    rw [abs_neg] at h2
    exact h2
  linarith only [hW, hcorr, htri]

/-- `(2 : ℝ) = 4096 ^ (1/12)`. -/
private lemma two_eq_4096_rpow : (2 : ℝ) = (4096 : ℝ) ^ (1 / 12 : ℝ) := by
  rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

-- FREE-nv-minimax task169 attempt: the direct IsLinearSieve projections for both leaves were tried and failed because the hypothesis has no such fields.

/-- LEAF. Wu 2004 page 39 equation 10.5, application of Lemmas 2.2 and 2.3.
This estimates only the count by its finite prime sum main term.
The replacement of li N by N over log N is included in the normalized error. -/
theorem main4_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        main4 f B N - η * Θ N ≤ sieveTerms N 4 := by
  sorry

set_option maxHeartbeats 8000000 in
/-- LEAF. Wu 2004 page 39 equation 10.5, replacement of prime sums by integrals.
The coprimality removal and finite logarithmic level loss belong to this limit.
There is no sieve count or Euler product in this statement. -/
theorem lowerSum4_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (lowerSum4 f B) evenAtTop (𝓝 (lowerIntegral4 f)) := by
  have hk1 : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk12 : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk24 : (2 : ℝ) * kappa2 ≤ 1 / 4 := kappa_bounds.2.2
  have hkq : kappa1 / 4 ≤ kappa2 := kappa_bounds.1
  set phi : ℝ → ℝ := fun s => f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) s)) / kappa1) with hphi
  have hphic : Continuous phi := clamped_phi_continuous h
  obtain ⟨Ck, hCk⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hphic.continuousOn (s := Set.Icc (kappa1 / 4) (3 * kappa2)))
  set W : ℝ → ℝ := fun x => ∫ u in x..kappa2,
      f ((1 / 2 - max (kappa1 / 2) (min (1 / 4) (x + u))) / kappa1) / u with hW
  have hWc : ContinuousOn W (Set.Icc (kappa1 / 4) (3 * kappa2)) := clampedWindow_continuous h
  obtain ⟨CW, hCW⟩ := isCompact_Icc.exists_bound_of_continuousOn hWc
  set C : ℝ := max (max Ck CW) 1 with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_right _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hkC : ∀ x ∈ Set.Icc (kappa1 / 4) (3 * kappa2), |phi x| ≤ C := by
    intro x hx
    have h1 : ‖phi x‖ ≤ Ck := hCk x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  have hWC : ∀ x ∈ Set.Icc (kappa1 / 4) (3 * kappa2), |W x| ≤ C := by
    intro x hx
    have h1 : ‖W x‖ ≤ CW := hCW x hx
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_trans (le_max_right _ _) (le_max_left _ _))
  have hii : ∀ a b : ℝ, kappa1 / 4 ≤ a → a ≤ b → b ≤ 3 * kappa2 →
      IntervalIntegrable (fun x : ℝ => W x / x) volume a b := by
    intro a b ha hab hb
    have hne : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => by
      have h1 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith only [hk1, ha]) hx.1
      exact ne_of_gt h1
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    refine (hWc.mono ?_).div continuousOn_id hne
    intro x hx
    exact ⟨by linarith only [hx.1, ha], by linarith only [hx.2, hb]⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hshK := band_limit_shift (k := phi) (C := C) hCpos hphic.continuousOn hkC hε8
  have hshW := band_limit_shift (k := W) (C := C) hCpos hWc hWC hε4
  have hlev := phi_shift F f h B hB (ε := ε / 8) hε8
  have hwt := band_weight_le_one
  have hbigA : ∀ᶠ N : ℕ in atTop, 8 * C * Real.log 2 / (kappa1 * ε) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (8 * C * Real.log 2 / (kappa1 * ε)))
  have hbigB : ∀ᶠ N : ℕ in atTop, 2 * Real.log 2 / kappa1 + 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 * Real.log 2 / kappa1 + 1))
  have key : ∀ᶠ N : ℕ in atTop, dist (lowerSum4 f B N) (lowerIntegral4 f) < ε := by
    filter_upwards [hshK, hshW, hlev, hwt, hbigA, hbigB, eventually_ge_atTop 16777216]
      with N hK hWb hL hwtN hbigAN hbigBN hNbig
    have hN2 : 2 ≤ N := by omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
    have hrpow1 : (0 : ℝ) < (N : ℝ) ^ kappa1 := Real.rpow_pos_of_pos hNpos _
    have hrpow2 : (0 : ℝ) < (N : ℝ) ^ kappa2 := Real.rpow_pos_of_pos hNpos _
    set n : ℕ := ⌈(N : ℝ) ^ kappa2⌉₊ - 1 with hn
    set m : ℕ := ⌈(N : ℝ) ^ kappa1⌉₊ - 1 with hm
    have hx2 : (2 : ℝ) ≤ (N : ℝ) ^ kappa1 := by
      rw [two_eq_4096_rpow]
      exact Real.rpow_le_rpow (by norm_num)
        (by exact_mod_cast (le_trans (by norm_num : (4096 : ℕ) ≤ 16777216) hNbig))
        (by norm_num)
    have hx4 : (4 : ℝ) ≤ (N : ℝ) ^ kappa1 := by
      have h1 : (4 : ℝ) = (16777216 : ℝ) ^ (1 / 12 : ℝ) := by
        rw [show (16777216 : ℝ) = 4 ^ 12 by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hNbig) (by norm_num)
    have hfloor1 : (1 : ℕ) ≤ ⌊(N : ℝ) ^ kappa1⌋₊ := Nat.le_floor (by
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ kappa1 := le_trans (by norm_num) hx2
      simpa using h2)
    have hceil1 : (1 : ℕ) ≤ ⌈(N : ℝ) ^ kappa1⌉₊ := Nat.ceil_pos.mpr hrpow1
    have hceil2 : (1 : ℕ) ≤ ⌈(N : ℝ) ^ kappa2⌉₊ := Nat.ceil_pos.mpr hrpow2
    have hmge : ⌊(N : ℝ) ^ kappa1⌋₊ - 1 ≤ m := by
      have h2 : ⌊(N : ℝ) ^ kappa1⌋₊ ≤ ⌈(N : ℝ) ^ kappa1⌉₊ := Nat.floor_le_ceil _
      omega
    have hnfl : n ≤ ⌊(N : ℝ) ^ kappa2⌋₊ := by
      have h2 : ⌈(N : ℝ) ^ kappa2⌉₊ - 1 ≤ ⌊(N : ℝ) ^ kappa2⌋₊ := ceil_sub_one_le_floor
      omega
    have hmn : m ≤ n := by
      have h2 : ⌈(N : ℝ) ^ kappa1⌉₊ ≤ ⌈(N : ℝ) ^ kappa2⌉₊ :=
        Nat.ceil_mono ((Real.rpow_le_rpow_left_iff hN1).mpr hk12.le)
      omega
    have hmR : (N : ℝ) ^ kappa1 / 2 ≤ (m : ℝ) := by
      have h4 : ((⌈(N : ℝ) ^ kappa1⌉₊ - 1 : ℕ) : ℝ)
          = ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub hceil1, Nat.cast_one]
      have h5 : (N : ℝ) ^ kappa1 ≤ ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h6 : ((m : ℕ) : ℝ) = ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) - 1 := hm ▸ h4
      linarith only [h5, h6, hx2]
    have hmle : (m : ℝ) ≤ (N : ℝ) ^ kappa1 := by
      have h4 : ((⌈(N : ℝ) ^ kappa1⌉₊ - 1 : ℕ) : ℝ)
          = ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub hceil1, Nat.cast_one]
      have h5 : ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) - 1 < (N : ℝ) ^ kappa1 := by
        have h6 := Nat.ceil_lt_add_one hrpow1.le
        linarith only [h6]
      have h6 : ((m : ℕ) : ℝ) = ((⌈(N : ℝ) ^ kappa1⌉₊ : ℕ) : ℝ) - 1 := hm ▸ h4
      linarith only [h5, h6]
    have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by positivity) hmR
    have hm1 : (1 : ℝ) < (m : ℝ) := by linarith only [hmpos, hmR, hx4]
    have hnR : (n : ℝ) ≤ (N : ℝ) ^ kappa2 := by
      have h4 : ((⌈(N : ℝ) ^ kappa2⌉₊ - 1 : ℕ) : ℝ)
          = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := by rw [Nat.cast_sub hceil2, Nat.cast_one]
      have h5 : ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 < (N : ℝ) ^ kappa2 := by
        have h6 := Nat.ceil_lt_add_one hrpow2.le
        linarith only [h6]
      have h6 : ((n : ℕ) : ℝ) = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := hn ▸ h4
      linarith only [h5, h6]
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hOwt : (∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        (1 : ℝ) / ((p : ℝ) - 1)) ≤ 1 := hwtN m n hmR hnR
    -- the level of a prime pair is the clamped argument
    have hlevel : ∀ p q : ℕ, p.Prime → q.Prime → p < q → (N : ℝ) ^ kappa1 ≤ (p : ℝ) →
        (q : ℝ) < (N : ℝ) ^ kappa2 →
        |f (lowerLevel B N (p * q))
          - phi (Real.log q / Real.log N + Real.log p / Real.log N)| ≤ ε / 8 := by
      intro p q hpprime hqprime hpq hpge hqle
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
      have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqprime.pos
      have h1 := hL p q hpprime hqprime hpq hpge hqle
      have hplo : kappa1 ≤ Real.log (p : ℝ) / Real.log N := by
        have h2 : Real.log ((N : ℝ) ^ kappa1) ≤ Real.log (p : ℝ) :=
          Real.log_le_log hrpow1 hpge
        rw [Real.log_rpow hNpos] at h2
        exact (le_div_iff₀ hlogN).mpr h2
      have hqge : kappa1 ≤ Real.log (q : ℝ) / Real.log N := by
        have h2 : Real.log ((N : ℝ) ^ kappa1) ≤ Real.log (q : ℝ) :=
          Real.log_le_log hrpow1 (le_trans hpge (by exact_mod_cast hpq.le))
        rw [Real.log_rpow hNpos] at h2
        exact (le_div_iff₀ hlogN).mpr h2
      have hqh : Real.log (q : ℝ) / Real.log N ≤ kappa2 := by
        have h2 : Real.log (q : ℝ) ≤ Real.log ((N : ℝ) ^ kappa2) :=
          le_of_lt (Real.log_lt_log hq0 hqle)
        rw [Real.log_rpow hNpos] at h2
        exact (div_le_iff₀ hlogN).mpr h2
      have hpl : Real.log (p : ℝ) / Real.log N ≤ kappa2 := by
        have h2 : (p : ℝ) < (N : ℝ) ^ kappa2 := lt_trans (by exact_mod_cast hpq) hqle
        have h3 : Real.log (p : ℝ) ≤ Real.log ((N : ℝ) ^ kappa2) :=
          le_of_lt (Real.log_lt_log hp0 h2)
        rw [Real.log_rpow hNpos] at h3
        exact (div_le_iff₀ hlogN).mpr h3
      have hsum_ge : kappa1 / 2 ≤
          Real.log (q : ℝ) / Real.log N + Real.log (p : ℝ) / Real.log N := by
        linarith only [hqge, hplo, hk1]
      have hsum_le : Real.log (q : ℝ) / Real.log N + Real.log (p : ℝ) / Real.log N ≤ 1 / 4 := by
        linarith only [hqh, hpl, hk24]
      have hphieq : phi (Real.log (q : ℝ) / Real.log N + Real.log (p : ℝ) / Real.log N)
          = f ((1 / 2 - (Real.log (p : ℝ) / Real.log N + Real.log (q : ℝ) / Real.log N))
              / kappa1) := by
        rw [hphi]
        simp only
        rw [min_eq_right hsum_le, max_eq_right hsum_ge]
        ring_nf
      rw [hphieq]
      exact h1
    -- the inner comparison, for one outer prime
    have hinner : ∀ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
        |(∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
            f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
          - W (Real.log p / Real.log N)| ≤ ε / 4 := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      obtain ⟨⟨hmp, hpn⟩, hpprime, hpcop⟩ := hp
      have hmp' : (⌈(N : ℝ) ^ kappa1⌉₊ - 1 : ℕ) < p := hm ▸ hmp
      have hpgeR : ⌈(N : ℝ) ^ kappa1⌉₊ ≤ p := by omega
      have hpge : (N : ℝ) ^ kappa1 ≤ (p : ℝ) := Nat.ceil_le.mp hpgeR
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
      have hpn' : p ≤ ⌈(N : ℝ) ^ kappa2⌉₊ - 1 := hn ▸ hpn
      have hnlt : ((⌈(N : ℝ) ^ kappa2⌉₊ - 1 : ℕ) : ℝ) < (N : ℝ) ^ kappa2 := by
        have h4 : ((⌈(N : ℝ) ^ kappa2⌉₊ - 1 : ℕ) : ℝ)
            = ((⌈(N : ℝ) ^ kappa2⌉₊ : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub hceil2, Nat.cast_one]
        have h6 := Nat.ceil_lt_add_one hrpow2.le
        linarith only [h4, h6]
      have htp : Real.log (p : ℝ) / Real.log N ∈ Set.Icc (0 : ℝ) kappa2 := by
        constructor
        · have h1 : Real.log ((N : ℝ) ^ kappa1) ≤ Real.log (p : ℝ) :=
            Real.log_le_log hrpow1 hpge
          rw [Real.log_rpow hNpos] at h1
          have h2 : kappa1 ≤ Real.log (p : ℝ) / Real.log N := (le_div_iff₀ hlogN).mpr h1
          linarith only [h2, hk1]
        · have h3 : Real.log (p : ℝ) ≤ Real.log ((N : ℝ) ^ kappa2) :=
            Real.log_le_log hp0 (le_of_lt (lt_of_le_of_lt (Nat.cast_le.mpr hpn') hnlt))
          rw [Real.log_rpow hNpos] at h3
          exact (div_le_iff₀ hlogN).mpr h3
      have hShK := hK (Real.log p / Real.log N) htp p
        (by omega) hpn'
      set I : Finset ℕ := (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N) with hI
      have hq3 : ∀ q ∈ I, (3 : ℝ) ≤ (q : ℝ) := by
        intro q hq
        simp only [hI, Finset.mem_filter, Finset.mem_Ioc] at hq
        have h4 : 2 ≤ p := hpprime.two_le
        have h5 : (3 : ℕ) ≤ q := by omega
        exact_mod_cast h5
      have hIwt : (∑ q ∈ I, (1 : ℝ) / ((q : ℝ) - 1)) ≤ 1 := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hOwt
        · intro q hq
          simp only [hI, Finset.mem_filter, Finset.mem_Ioc] at hq ⊢
          exact ⟨⟨by omega, by omega⟩, hq.2⟩
        · intro q hq hqn
          have h4 : (2 : ℕ) ≤ q := (Finset.mem_filter.mp hq).2.1.two_le
          have h5 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h4
          exact div_nonneg zero_le_one (by linarith)
      have hdecomp : (∑ q ∈ I, f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
          = (∑ q ∈ I, (f (lowerLevel B N (p * q))
              - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1))
            + ∑ q ∈ I,
                phi (Real.log q / Real.log N + Real.log p / Real.log N) / ((q : ℝ) - 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q hq => ?_
        have h3 : ((q : ℝ) - 1) ≠ 0 := by
          have := hq3 q hq
          linarith
        field_simp
        ring
      have hShK' : |(∑ q ∈ I,
            phi (Real.log q / Real.log N + Real.log p / Real.log N) / ((q : ℝ) - 1))
          - W (Real.log p / Real.log N)| ≤ ε / 8 := by
        rw [hW]
        simpa only [hphi, add_comm (Real.log p / Real.log N)] using hShK
      have hdiff : |(∑ q ∈ I, (f (lowerLevel B N (p * q))
            - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1))|
          ≤ ε / 8 := by
        have hstep : ∀ q ∈ I, |(f (lowerLevel B N (p * q))
            - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1)|
            ≤ (ε / 8) * (1 / ((q : ℝ) - 1)) := by
          intro q hq
          simp only [hI, Finset.mem_filter, Finset.mem_Ioc] at hq
          obtain ⟨⟨hpq, hqn⟩, hqprime, hqcop⟩ := hq
          have hqn' : q ≤ ⌈(N : ℝ) ^ kappa2⌉₊ - 1 := hn ▸ hqn
          have hq_lt : (q : ℝ) < (N : ℝ) ^ kappa2 :=
            lt_of_le_of_lt (Nat.cast_le.mpr hqn') hnlt
          have h3 : (0 : ℝ) < (q : ℝ) - 1 := by
            have h4 : 2 ≤ q := hqprime.two_le
            have h5 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h4
            linarith
          have h4 := hlevel p q hpprime hqprime hpq hpge hq_lt
          rw [abs_div, abs_of_pos h3, div_eq_mul_inv]
          simpa only [one_div, mul_one] using
            mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ ((q : ℝ) - 1)⁻¹)
        calc |∑ q ∈ I, (f (lowerLevel B N (p * q))
              - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1)|
            ≤ ∑ q ∈ I, |(f (lowerLevel B N (p * q))
              - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q ∈ I, (ε / 8) * (1 / ((q : ℝ) - 1)) := Finset.sum_le_sum hstep
          _ = (ε / 8) * ∑ q ∈ I, (1 / ((q : ℝ) - 1)) := by rw [Finset.mul_sum]
          _ ≤ (ε / 8) * 1 := mul_le_mul_of_nonneg_left hIwt (by linarith)
          _ = ε / 8 := by ring
      have hre : (∑ q ∈ I, f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
            - W (Real.log p / Real.log N)
          = (∑ q ∈ I, (f (lowerLevel B N (p * q))
              - phi (Real.log q / Real.log N + Real.log p / Real.log N)) / ((q : ℝ) - 1))
            + ((∑ q ∈ I, phi (Real.log q / Real.log N + Real.log p / Real.log N)
                / ((q : ℝ) - 1)) - W (Real.log p / Real.log N)) := by
        rw [hdecomp]
        ring
      rw [hre]
      refine le_trans (abs_add_le _ _) ?_
      linarith only [hShK', hdiff]
    -- the outer comparison
    have hOut : |(∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
          W (Real.log p / Real.log N) / ((p : ℝ) - 1))
        - ∫ x in (Real.log m / Real.log N)..kappa2, W x / x| ≤ ε / 4 := by
      have h1 := hWb 0 ⟨le_rfl, hk2.le⟩ m hmge hmn
      simpa only [add_zero] using h1
    -- the lower endpoint correction
    have hlog2N : Real.log 2 / Real.log N ≤ kappa1 / 2 := by
      rw [div_le_iff₀ hlogN]
      have h3 := mul_le_mul_of_nonneg_left hbigBN hk1.le
      have h4 : kappa1 * (2 * Real.log 2 / kappa1 + 1) = 2 * Real.log 2 + kappa1 := by
        field_simp
      rw [h4] at h3
      linarith only [h3, hk1]
    have hlogm_lo : kappa1 - Real.log 2 / Real.log N ≤ Real.log (m : ℝ) / Real.log N := by
      have h5 : Real.log ((N : ℝ) ^ kappa1 / 2) ≤ Real.log (m : ℝ) :=
        Real.log_le_log (by positivity) hmR
      rw [Real.log_div hrpow1.ne' (by norm_num), Real.log_rpow hNpos] at h5
      rw [le_div_iff₀ hlogN]
      have h6 : (kappa1 - Real.log 2 / Real.log N) * Real.log (N : ℝ)
          = kappa1 * Real.log (N : ℝ) - Real.log 2 := by
        field_simp
      rw [h6]
      linarith only [h5]
    have ha_low : kappa1 / 2 ≤ Real.log (m : ℝ) / Real.log N := by
      linarith only [hlogm_lo, hlog2N]
    have hab : Real.log (m : ℝ) / Real.log N ≤ kappa1 := by
      have h2 : Real.log (m : ℝ) ≤ Real.log ((N : ℝ) ^ kappa1) :=
        Real.log_le_log hmpos hmle
      rw [Real.log_rpow hNpos] at h2
      exact (div_le_iff₀ hlogN).mpr h2
    have hgapend : |∫ x in (Real.log m / Real.log N)..kappa1, W x / x| ≤ ε / 4 := by
      have ha : (0 : ℝ) < Real.log (m : ℝ) / Real.log N :=
        div_pos (Real.log_pos hm1) hlogN
      have hcont : ContinuousOn W (Set.Icc (Real.log (m : ℝ) / Real.log N) kappa1) :=
        hWc.mono fun x hx =>
          ⟨by linarith only [hx.1, ha_low, hk1], by linarith only [hx.2, hk12, hk2]⟩
      have hb := abs_integral_div_sub_const_le (g := W)
        (a := Real.log (m : ℝ) / Real.log N) (b := kappa1) (c := 0) (C := C) ha hab hcont
        (fun x hx => by
          have h1 : |W x| ≤ C := hWC x ⟨by linarith only [hx.1, ha_low, hk1],
            by linarith only [hx.2, hk12, hk2]⟩
          simpa only [sub_zero] using h1)
      simp only [zero_mul, sub_zero] at hb
      have hstep : Real.log kappa1 - Real.log (Real.log (m : ℝ) / Real.log N)
          ≤ 2 * Real.log 2 / (kappa1 * Real.log N) := by
        have h1 : Real.log kappa1 - Real.log (Real.log (m : ℝ) / Real.log N)
            ≤ (Real.log 2 / Real.log N) / (kappa1 / 2) :=
          log_sub_log_le_div hk1 ha (by linarith only [hk1]) ha_low
            (by linarith only [hlogm_lo]) (by positivity)
        have h2 : (Real.log 2 / Real.log N) / (kappa1 / 2)
            = 2 * Real.log 2 / (kappa1 * Real.log N) := by
          field_simp
        linarith only [h1, h2]
      have harith : C * (2 * Real.log 2 / (kappa1 * Real.log N)) ≤ ε / 4 := by
        have h1 : 8 * C * Real.log 2 ≤ kappa1 * ε * Real.log N := by
          have h2 := mul_le_mul_of_nonneg_right hbigAN (le_of_lt (mul_pos hk1 hε))
          rwa [div_mul_cancel₀ (8 * C * Real.log 2) (ne_of_gt (mul_pos hk1 hε)),
            mul_comm (Real.log (N : ℝ))] at h2
        rw [← mul_div_assoc]
        rw [div_le_iff₀ (mul_pos hk1 hlogN)]
        nlinarith only [h1, hlogN, hk1, hε.le]
      linarith only [hb, mul_le_mul_of_nonneg_left hstep (by linarith only [hC1] : (0:ℝ) ≤ C),
        harith]
    -- identify the window integral with `lowerIntegral4`
    have hId : (∫ x in kappa1..kappa2, W x / x) = lowerIntegral4 f := by
      rw [lowerIntegral4_eq]
      refine intervalIntegral.integral_congr fun t ht => ?_
      have ht' : t ∈ Set.Icc kappa1 kappa2 :=
        Set.uIcc_subset_Icc ⟨le_rfl, hk12.le⟩ ⟨hk12.le, le_rfl⟩ ht
      rw [hW]
      exact congrArg (fun v => v / t) (clampedWindow_eq ht')
    -- assemble
    have hSiter : lowerSum4 f B N =
        ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
          (1 : ℝ) / ((p : ℝ) - 1) *
            ∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
              f (lowerLevel B N (p * q)) / ((q : ℝ) - 1) :=
      lowerSum4_iterate hN2 B f
    rw [hSiter, Real.dist_eq]
    set S : ℝ := ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
      (1 : ℝ) / ((p : ℝ) - 1) *
        ∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
          f (lowerLevel B N (p * q)) / ((q : ℝ) - 1) with hS
    set T : ℝ := ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
      W (Real.log p / Real.log N) / ((p : ℝ) - 1) with hT
    set I2 : ℝ := ∫ x in (Real.log m / Real.log N)..kappa2, W x / x with hI2
    have hST : |S - T| ≤ ε / 4 := by
      have hcomp : S - T = ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
          (1 : ℝ) / ((p : ℝ) - 1) *
            ((∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
                f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
              - W (Real.log p / Real.log N)) := by
        rw [hS, hT, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        ring
      rw [hcomp]
      calc |∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
            (1 : ℝ) / ((p : ℝ) - 1) *
              ((∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
                  f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
                - W (Real.log p / Real.log N))|
          ≤ ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
            |(1 : ℝ) / ((p : ℝ) - 1) *
              ((∑ q ∈ (Finset.Ioc p n).filter (fun q => q.Prime ∧ q.Coprime N),
                  f (lowerLevel B N (p * q)) / ((q : ℝ) - 1))
                - W (Real.log p / Real.log N))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
            (1 : ℝ) / ((p : ℝ) - 1) * (ε / 4) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
              have h2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.1.two_le
              exact_mod_cast h2
            have hw : (0 : ℝ) < (1 : ℝ) / ((p : ℝ) - 1) := by
              apply div_pos one_pos
              linarith only [hp2]
            rw [abs_mul, abs_of_pos hw]
            exact mul_le_mul_of_nonneg_left (hinner p hp) hw.le
        _ = (ε / 4) * ∑ p ∈ (Finset.Ioc m n).filter (fun p => p.Prime ∧ p.Coprime N),
            (1 : ℝ) / ((p : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun p hp => ?_
            ring
        _ ≤ (ε / 4) * 1 := mul_le_mul_of_nonneg_left hOwt (by linarith only [hε4])
        _ = ε / 4 := by ring
    have hI2T : |T - I2| ≤ ε / 4 := by
      rw [hT, hI2]
      exact hOut
    have halg : S - lowerIntegral4 f = (S - T) + (T - I2)
        + ∫ x in (Real.log m / Real.log N)..kappa1, W x / x := by
      have h3 : I2 = (∫ x in (Real.log m / Real.log N)..kappa1, W x / x)
          + lowerIntegral4 f := by
        rw [hI2, ← hId]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hii (Real.log (m : ℝ) / Real.log N) kappa1 (by linarith only [ha_low, hk1])
            (by linarith only [hab, hk1]) (by linarith only [hk12, hk2]))
          (hii kappa1 kappa2 (by linarith only [hk1]) (by linarith only [hk12])
            (by linarith only [hk2]))).symm
      linarith only [h3]
    rw [halg]
    have e1 := abs_add_le (S - T) (T - I2)
    have e2 := abs_add_le ((S - T) + (T - I2))
      (∫ x in (Real.log m / Real.log N)..kappa1, W x / x)
    linarith only [e1, e2, hST, hI2T, hgapend, hε]
  exact key.filter_mono inf_le_left

/-- Exact normalization of the finite Upsilon 4 main term. -/
theorem main4_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main4 f B N / Θ N = scaledDensity N * lowerSum4 f B N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold main4 scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']
  <;> ring

/-- The finite Upsilon 4 main term tends to its exact integral coefficient.
CONDITIONAL ON the two OPEN normalization limits and IsLinearSieve. -/
theorem main4_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N => main4 f B N / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 4)) := by
  have ht := scaledDensity_tendsto.mul (lowerSum4_tendsto F f h B hB)
  have ht' : Tendsto (fun N => scaledDensity N * lowerSum4 f B N)
      evenAtTop (𝓝 (integralTerms F f ω 4)) := by
    convert ht using 1
    change 𝓝 (2 / (kappa1 * exp eulerMascheroniConstant) * lowerIntegral4 f) = _
    rfl
  apply ht'.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  exact (main4_ratio f B hN).symm

/-- The exact lower_F4 conclusion follows from strictly smaller analytic leaves.
OPEN through main4_lower, lowerSum4_tendsto and scaledDensity_tendsto. -/
theorem lower_F4_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  exact lower_of_main _ _ (main4 f) (main4_lower F f h)
    (fun B hB => main4_tendsto F f ω h B hB)

end LeanLab.ChenDoubleSieve.Task348
