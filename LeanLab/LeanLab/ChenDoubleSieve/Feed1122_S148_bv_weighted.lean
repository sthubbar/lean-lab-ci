import LeanLab.ChenDoubleSieve.Decomp363b

/-!
# The tau weighted Bombieri Vinogradov remainder for the prime difference sequence

Source: Wu 2004, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
https://arxiv.org/pdf/0705.1652, page 38, the display before 10.3, with Lemma 2.3 on page 6.

The weighted sum over q coprime to N of tau(q) times the discrepancy
`|#{N - p : q divides N - p} - pi(N) / phi(q)|` is at most `K N / (log N)^3`.
The proof: Cauchy Schwarz against the unweighted Bombieri Vinogradov bound
`bvPi` of `LeanLab.PNTPort.BVMax`, the trivial bound `count <= N / q + 1`,
the prime number theorem with error term read off the q = 1 term of the same
Bombieri Vinogradov sum, and the classical divisor moment
`sum_{q <= Q} tau(q)^2 / phi(q) << (1 + log Q)^4`, which is the one LEAF.

AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S148
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve)

/-- LEAF: classical divisor moment, sum over q at most Q of tau(q)^2 / phi(q) is O((1 + log Q)^4),
used in Wu 2004 page 38 to pass from Lemma 2.3 to the tau weighted remainder. MEDIUM -/
theorem leaf_tau_sq_div_totient_moment :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℕ,
      ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ) ≤
        K * (1 + Real.log Q) ^ 4 := by
  sorry

/-- Number of elements of `primeSequence N` divisible by `q` is at most `N / q + 1`. -/
private theorem card_filter_dvd_le (N q : ℕ) (hq : 1 ≤ q) :
    (((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) ≤ (N : ℝ) / q + 1 := by
  have hsub : (primeSequence N).filter (fun a => q ∣ a) ⊆
      insert 0 ((Finset.Ioc 0 N).filter (fun a => q ∣ a)) := by
    intro a ha
    simp only [primeSequence, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨⟨p, ⟨hp, _⟩, rfl⟩, hd⟩ := ha
    rcases Nat.eq_zero_or_pos (N - p) with h0 | h0
    · rw [h0]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨h0, by omega⟩, hd⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le 0 ((Finset.Ioc 0 N).filter (fun a => q ∣ a))
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h2
  have h3 : (((N / q : ℕ)) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  have h4 : (((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast h1.trans h2
  linarith

/-- The count of `primeSequence N` is the prime count. -/
private theorem card_primeSequence (N : ℕ) :
    (primeSequence N).card = ((Finset.range (N + 1)).filter Nat.Prime).card := by
  unfold primeSequence
  apply Finset.card_image_of_injOn
  intro a ha b hb h
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
  simp only at h
  omega

/-- Final arithmetic: from Cauchy Schwarz. -/
private theorem final_arith (X a b α β n L : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hL : 1 ≤ L)
    (hXab : X ^ 2 ≤ a * b) (haα : a ≤ α * n / L ^ 10) (hbβ : b ≤ β * n * L ^ 4) :
    X ≤ (Real.sqrt (α * β) + 1) * n / L ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hL3 : 0 < L ^ 3 := by positivity
  have hab : a * b ≤ (α * n / L ^ 10) * (β * n * L ^ 4) :=
    mul_le_mul haα hbβ hb (by positivity)
  have heq : (α * n / L ^ 10) * (β * n * L ^ 4) = (Real.sqrt (α * β) * n / L ^ 3) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hα hβ)]
    field_simp
  have hsq : X ^ 2 ≤ (Real.sqrt (α * β) * n / L ^ 3) ^ 2 := by linarith
  have hX' : X ≤ Real.sqrt (α * β) * n / L ^ 3 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have : Real.sqrt (α * β) * n / L ^ 3 ≤ (Real.sqrt (α * β) + 1) * n / L ^ 3 := by
    apply div_le_div_of_nonneg_right _ hL3.le
    nlinarith
  linarith

/-- Assembly: Cauchy Schwarz from an unweighted Bombieri Vinogradov bound with main term `Lf N`.
Wu 2004 page 38, display before 10.3. -/
private theorem weighted_of_bv (Lf : ℕ → ℝ)
    (hbv : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
          Lf N / (d.totient : ℝ)| ≤ K * N / Real.log N ^ A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∑ q ∈ (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌉₊).filter
            (fun q => q.Coprime N),
          (q.divisors.card : ℝ) *
            |(((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) -
              (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤
          K * N / (log N) ^ 3 := by
  obtain ⟨B, hB, K, hK⟩ := hbv 14 (by norm_num)
  obtain ⟨Km, hKm0, hKm⟩ := leaf_tau_sq_div_totient_moment
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set α := K' * (1 + 16 * Km) with hα
  set β := 64 * Km with hβ
  refine ⟨B, hB, Real.sqrt (α * β) + 1, by positivity, 3, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log N with hLdef
  set P : ℝ := (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) with hP
  set M := ⌊Real.sqrt N / L ^ B⌋₊ with hM
  set S := (Finset.Icc 1 M).filter (fun d => Nat.Coprime N d) with hS
  set c : ℕ → ℝ := fun q => (((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) with hc
  -- step 1: the target range is inside S
  have hsub : (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / L ^ B⌉₊).filter
      (fun q => q.Coprime N) ⊆ S := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hq1, hq2⟩ := hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hq2
      omega
    have hlt : (q : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / L ^ B := Nat.lt_ceil.mp hq1
    rw [← Real.sqrt_eq_rpow] at hlt
    simp only [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hq0, Nat.le_floor hlt.le⟩, hq2.symm⟩
  have hstep1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q => (q.divisors.card : ℝ) * |c q - P / (q.totient : ℝ)|)
    (fun q _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  refine le_trans hstep1 ?_
  have hL3 : 0 < L ^ 3 := by positivity
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · have : S = ∅ := by
      rw [hS, hM0]; rfl
    rw [this, Finset.sum_empty]
    positivity
  have hLB : 1 ≤ L ^ B := Real.one_le_rpow hL hB.le
  have hMN : (M : ℝ) ≤ N := by
    have h1 : (M : ℝ) ≤ Real.sqrt N / L ^ B := Nat.floor_le (by positivity)
    have h2 : Real.sqrt N / L ^ B ≤ Real.sqrt N := div_le_self (Real.sqrt_nonneg _) hLB
    have h3 : Real.sqrt N ≤ N := by
      rw [Real.sqrt_le_iff]; constructor <;> nlinarith
    linarith
  have hqS : ∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) ≤ N := by
    intro q hq
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hq
    refine ⟨hq.1.1, ?_⟩
    have : (q : ℝ) ≤ M := by exact_mod_cast hq.1.2
    linarith
  have hphi : ∀ q ∈ S, 0 < (q.totient : ℝ) := by
    intro q hq
    exact_mod_cast Nat.totient_pos.mpr (hqS q hq).1
  have hbvN := hK N hN2
  have h14 : L ^ (14 : ℝ) = L ^ (14 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  set T := K' * N / L ^ (14 : ℕ) with hT
  have hT0 : 0 ≤ T := by positivity
  have hD : ∑ q ∈ S, |c q - Lf N / (q.totient : ℝ)| ≤ T := by
    have : K * N / L ^ (14 : ℝ) ≤ T := by
      rw [h14, hT]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
    exact le_trans hbvN this
  have h1S : 1 ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hM0⟩, Nat.coprime_one_right _⟩
  have herr : |P - Lf N| ≤ T := by
    have h1 := Finset.single_le_sum (f := fun q => |c q - Lf N / (q.totient : ℝ)|)
      (fun q _ => abs_nonneg _) h1S
    have hc1 : c 1 = P := by
      simp only [hc, Nat.one_dvd, Finset.filter_true]
      rw [card_primeSequence]
    simp only [hc1, Nat.totient_one, Nat.cast_one, div_one] at h1
    linarith
  have hmomS : ∑ q ∈ S, (q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ) ≤ 16 * Km * L ^ 4 := by
    have h1 : ∑ q ∈ S, (q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ) ≤
        ∑ q ∈ Finset.Icc 1 M, (q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun q _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    have h2 := hKm M
    have hlogM : Real.log M ≤ L := Real.log_le_log (by exact_mod_cast hM0) hMN
    have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM0)
    have h3 : (1 + Real.log M) ^ 4 ≤ (2 * L) ^ 4 := by
      apply pow_le_pow_left₀ (by linarith); linarith
    have h4 : Km * (1 + Real.log M) ^ 4 ≤ 16 * Km * L ^ 4 := by
      have := mul_le_mul_of_nonneg_left h3 hKm0
      nlinarith
    linarith
  have hinv : ∑ q ∈ S, 1 / (q.totient : ℝ) ≤ 16 * Km * L ^ 4 := by
    refine le_trans (Finset.sum_le_sum fun q hq => ?_) hmomS
    apply div_le_div_of_nonneg_right _ (hphi q hq).le
    have : (1 : ℝ) ≤ q.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by have := (hqS q hq).1; omega)⟩
    nlinarith
  have hE1 : ∀ q ∈ S, |c q - P / (q.totient : ℝ)| ≤
      |c q - Lf N / (q.totient : ℝ)| + |P - Lf N| * (1 / (q.totient : ℝ)) := by
    intro q hq
    have hp := hphi q hq
    have : c q - P / (q.totient : ℝ) = (c q - Lf N / (q.totient : ℝ)) - (P - Lf N) / (q.totient : ℝ) := by
      field_simp; ring
    rw [this]
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hp]; ring
  have hE2 : ∀ q ∈ S, |c q - P / (q.totient : ℝ)| ≤ 4 * N * (1 / (q.totient : ℝ)) := by
    intro q hq
    have hp := hphi q hq
    obtain ⟨hq1, hqN⟩ := hqS q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have htq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hc1 : c q ≤ N / q + 1 := card_filter_dvd_le N q hq1
    have hc0 : 0 ≤ c q := Nat.cast_nonneg _
    have hPle : P ≤ N + 1 := by
      have : ((Finset.range (N + 1)).filter Nat.Prime).card ≤ N + 1 :=
        (Finset.card_filter_le _ _).trans (by simp)
      simp only [hP]; exact_mod_cast this
    have hP0 : 0 ≤ P := Nat.cast_nonneg _
    have hNq : (N : ℝ) / q ≤ N / q.totient := div_le_div_of_nonneg_left (by positivity) hp htq
    have h1q : (1 : ℝ) ≤ N / q.totient := by rw [le_div_iff₀ hp]; linarith
    have hPq : P / q.totient ≤ 2 * (N / q.totient) := by
      rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ hp.le; linarith
    have hPq0 : 0 ≤ P / q.totient := div_nonneg hP0 hp.le
    rw [abs_le]
    constructor
    · have : 4 * (N : ℝ) * (1 / q.totient) = 4 * (N / q.totient) := by ring
      rw [this]; linarith
    · have : 4 * (N : ℝ) * (1 / q.totient) = 4 * (N / q.totient) := by ring
      rw [this]; linarith
  -- sums
  have hsumE : ∑ q ∈ S, |c q - P / (q.totient : ℝ)| ≤ α * N / L ^ 10 := by
    have h1 : ∑ q ∈ S, |c q - P / (q.totient : ℝ)| ≤
        ∑ q ∈ S, |c q - Lf N / (q.totient : ℝ)| + |P - Lf N| * ∑ q ∈ S, 1 / (q.totient : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hE1
    have h2 : |P - Lf N| * ∑ q ∈ S, 1 / (q.totient : ℝ) ≤ T * (16 * Km * L ^ 4) :=
      mul_le_mul herr hinv (Finset.sum_nonneg fun q hq => (one_div_pos.mpr (hphi q hq)).le) hT0
    have h3 : T + T * (16 * Km * L ^ 4) ≤ α * N / L ^ 10 := by
      have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL
      have hL0 : 0 < L := by linarith
      have e1 : T = K' * N / L ^ 10 * (1 / L ^ 4) := by
        rw [hT]; field_simp
      rw [e1, hα]
      have hX : 0 ≤ K' * N / L ^ 10 := by positivity
      have hinvL : 1 / L ^ 4 ≤ 1 := by rw [div_le_one (by positivity)]; exact hL4
      have : K' * N / L ^ 10 * (1 / L ^ 4) * (16 * Km * L ^ 4) = K' * N / L ^ 10 * (16 * Km) := by
        field_simp
      rw [this]
      have : K' * ↑N / L ^ 10 * (1 / L ^ 4) ≤ K' * N / L ^ 10 := by
        nlinarith [mul_le_mul_of_nonneg_left hinvL hX]
      have e2 : K' * (1 + 16 * Km) * N / L ^ 10 = K' * N / L ^ 10 + K' * N / L ^ 10 * (16 * Km) := by
        ring
      rw [e2]; linarith
    linarith
  have hsumE2 : ∑ q ∈ S, (q.divisors.card : ℝ) ^ 2 * |c q - P / (q.totient : ℝ)| ≤ β * N * L ^ 4 := by
    have h1 : ∑ q ∈ S, (q.divisors.card : ℝ) ^ 2 * |c q - P / (q.totient : ℝ)| ≤
        ∑ q ∈ S, 4 * N * ((q.divisors.card : ℝ) ^ 2 / (q.totient : ℝ)) := by
      refine Finset.sum_le_sum fun q hq => ?_
      have := mul_le_mul_of_nonneg_left (hE2 q hq) (sq_nonneg (q.divisors.card : ℝ))
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [← Finset.mul_sum] at h1
    have h2 := mul_le_mul_of_nonneg_left hmomS (by positivity : (0 : ℝ) ≤ 4 * N)
    rw [hβ]; nlinarith
  have hCS : (∑ q ∈ S, (q.divisors.card : ℝ) * |c q - P / (q.totient : ℝ)|) ^ 2 ≤
      (∑ q ∈ S, |c q - P / (q.totient : ℝ)|) *
        ∑ q ∈ S, (q.divisors.card : ℝ) ^ 2 * |c q - P / (q.totient : ℝ)| := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro q _; exact abs_nonneg _
    · intro q _; exact mul_nonneg (sq_nonneg _) (abs_nonneg _)
    · intro q _; exact le_of_eq (by ring)
  exact final_arith _ _ _ α β N L
    (Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg fun q _ => abs_nonneg _)
    (Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (abs_nonneg _))
    (by positivity) (by positivity) (Nat.cast_nonneg _) hL hCS hsumE hsumE2

section BVCopy
open LeanLab.PNTPort.BVMax

/-- Copied from `LeanLab/ChenDoubleSieve/Decomp363b.lean`, where it is private:
the sieve remainder of `primeSequence N` at modulus `d` is `pi(N; d, N)`. -/
private theorem card_dvd_primeSequence_S148 (N d : ℕ) (hd : 1 ≤ d) :
    (((primeSequence N).filter (fun m => d ∣ m)).card : ℝ) = piN N d N := by
  unfold primeSequence piN
  rw [filter_image, card_image_of_injOn]
  · congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, Function.comp]
    constructor
    · rintro ⟨⟨hp, hpr⟩, hdvd⟩
      exact ⟨⟨hpr.one_lt.le, by omega⟩, ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd), hpr⟩
    · rintro ⟨⟨h1, h2⟩, hmod, hpr⟩
      exact ⟨⟨by omega, hpr⟩, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
  · intro a ha b hb he
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
    simp only at he
    omega

/-- Copied from `LeanLab/ChenDoubleSieve/Decomp363b.lean`, where it is private:
Bombieri Vinogradov for the difference sequence `{N - p : p <= N prime}`,
unconditional through `bvPi`. -/
private theorem bvPrimeSequence_S148 (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
          liD (N : ℝ) / (d.totient : ℝ)| ≤ K * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK⟩ := bvPi A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => (N : ℝ)) (fun _ => ⟨by positivity, le_rfl⟩)
  refine le_trans ?_ hbv
  have hEq : ∀ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
        (fun d => Nat.Coprime N d),
      |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
          liD (N : ℝ) / (d.totient : ℝ)|
        = |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| := by
    intro d hd
    rw [mem_filter] at hd
    have had : a d = N := by simp only [ha]; rw [if_pos hd.2]
    rw [had, card_dvd_primeSequence_S148 N d (by rw [Finset.mem_Icc] at hd; omega)]
    simp only [piAP, Nat.floor_natCast]
  calc ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |((((primeSequence N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
            liD (N : ℝ) / (d.totient : ℝ)|
      = ∑ d ∈ (Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter
          (fun d => Nat.Coprime N d),
        |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| :=
        sum_congr rfl hEq
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊,
        |piAP (N : ℝ) d (a d) - liD (N : ℝ) / (d.totient : ℝ)| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)

end BVCopy

/-- Wu 2004 page 38, display before 10.3, from Lemma 2.3: the tau weighted
Bombieri Vinogradov remainder with main term pi(N) / phi(q). -/
theorem leaf_bv_weighted_pi_proved :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ q ∈ (Finset.range ⌈(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌉₊).filter
          (fun q => q.Coprime N),
        (q.divisors.card : ℝ) *
          |(((primeSequence N).filter (fun a => q ∣ a)).card : ℝ) -
            (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤
        K * N / (log N) ^ 3 :=
  weighted_of_bv (fun N => LeanLab.PNTPort.BVMax.liD (N : ℝ)) bvPrimeSequence_S148

end LeanLab.ChenDoubleSieve.Feed1122.S148
