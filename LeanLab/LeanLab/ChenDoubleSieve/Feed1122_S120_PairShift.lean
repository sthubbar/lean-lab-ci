import LeanLab.ChenDoubleSieve.Decomp348b

/-!
Shift lemmas for the prime pair sums of Wu 2004 Section 10, page 39, equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39.
The finite level `lowerLevel B N (p q)` differs from the limiting argument
`(1/2 - log p / log N - log q / log N) / κ₁` by `12 B log log N / log N`, which tends to
zero; with uniform continuity of `f` on a compact window and a bounded pair weight sum,
the two weighted prime pair sums differ by `o(1)`. The weight sum is bounded by the band
form of Mertens' second theorem, `Task348.band_prime_inv`.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task315.FeedS120
open Task275

/-- The finite level at a prime pair is the limiting argument shifted by
`12 B log log N / log N`, Wu 2004 page 39. -/
theorem lowerLevel_pair' {N : ℕ} (hN : 3 ≤ N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (B : ℝ) :
    Task348.lowerLevel B N (p * q)
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
  unfold Task348.lowerLevel
  rw [Real.log_div hnumpos.ne' hcast.ne',
    Real.log_div (Real.rpow_pos_of_pos hNpos _).ne' (Real.rpow_pos_of_pos hlogN B).ne',
    Real.log_rpow hNpos, Real.log_rpow hlogN, hden, Nat.cast_mul,
    Real.log_mul hp0.ne' hq0.ne']
  simp only [kappa1]
  have h1 : Real.log (N : ℝ) ≠ 0 := hlogN.ne'
  have h2 : Real.log (N : ℝ) / 12 ≠ 0 := by positivity
  field_simp
  ring

/-- Totient of a product of two distinct primes. -/
theorem totient_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (Nat.totient (p * q) : ℝ) = ((p : ℝ) - 1) * ((q : ℝ) - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hne), Nat.totient_prime hp,
    Nat.totient_prime hq, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_sub hq.one_le]
  simp

/-- The pair weight is at most four times the product of the prime reciprocals,
summed over a product of bands. -/
theorem pair_weight_le (P : Finset (ℕ × ℕ)) (hP : ∀ q ∈ P, 2 ≤ q.1 ∧ 2 ≤ q.2) :
    ∑ q ∈ P, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) ≤
      4 * ((∑ p ∈ P.image Prod.fst, (1 : ℝ) / p) *
        (∑ r ∈ P.image Prod.snd, (1 : ℝ) / r)) := by
  have hsub : P ⊆ (P.image Prod.fst) ×ˢ (P.image Prod.snd) := by
    intro q hq
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  have hpt : ∀ q ∈ P, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) ≤
      4 * ((1 : ℝ) / q.1 * (1 / q.2)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hP q hq
    have a1 : (2 : ℝ) ≤ q.1 := by exact_mod_cast h1
    have a2 : (2 : ℝ) ≤ q.2 := by exact_mod_cast h2
    rw [div_le_iff₀ (by nlinarith)]
    field_simp
    nlinarith
  calc ∑ q ∈ P, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))
      ≤ ∑ q ∈ P, 4 * ((1 : ℝ) / q.1 * (1 / q.2)) := Finset.sum_le_sum hpt
    _ ≤ ∑ q ∈ (P.image Prod.fst) ×ˢ (P.image Prod.snd), 4 * ((1 : ℝ) / q.1 * (1 / q.2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = 4 * ((∑ p ∈ P.image Prod.fst, (1 : ℝ) / p) *
        (∑ r ∈ P.image Prod.snd, (1 : ℝ) / r)) := by
        rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_mul_sum]

/-- Band form of Mertens' second theorem gives a uniform bound for the reciprocal
prime sum over any set of primes in `[N^a, N^b]`, Wu 2004 page 39. -/
theorem band_recip_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ s : Finset ℕ,
      (∀ p ∈ s, p.Prime ∧ (N : ℝ) ^ a ≤ p ∧ (p : ℝ) ≤ (N : ℝ) ^ b) →
        ∑ p ∈ s, (1 : ℝ) / p ≤ C := by
  have hm := Task348.band_prime_inv (a / 2) b (by positivity) (by linarith)
  set L := Real.log b - Real.log (a / 2)
  refine ⟨max (L + 1) 0, le_max_right _ _, ?_⟩
  filter_upwards [hm.eventually (eventually_le_nhds (by linarith : L < L + 1)),
    eventually_ge_atTop 2] with N hN hN2 s hs
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hsub : s ⊆ (Finset.Ioc ⌊(N : ℝ) ^ (a / 2)⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, hlo, hhi⟩ := hs p hp
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, Nat.le_floor hhi⟩, hpr⟩
    have h1 : (⌊(N : ℝ) ^ (a / 2)⌋₊ : ℝ) < p := by
      have := Nat.floor_le (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N) (a / 2))
      have := Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith : a / 2 < a)
      linarith
    exact_mod_cast h1
  calc ∑ p ∈ s, (1 : ℝ) / p
      ≤ ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ (a / 2)⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ L + 1 := hN
    _ ≤ max (L + 1) 0 := le_max_left _ _

/-- Logarithmic band position from a lower power bound. -/
theorem le_logdiv {N : ℕ} (hN : 2 ≤ N) {a x : ℝ} (hx : (N : ℝ) ^ a ≤ x) :
    a ≤ Real.log x / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h := Real.log_le_log (Real.rpow_pos_of_pos hN0 a) hx
  rw [Real.log_rpow hN0] at h
  rw [le_div_iff₀ hlog]
  linarith

/-- Logarithmic band position from an upper power bound. -/
theorem logdiv_lt {N : ℕ} (hN : 2 ≤ N) {a x : ℝ} (hx0 : 0 < x) (hx : x < (N : ℝ) ^ a) :
    Real.log x / Real.log N < a := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have h := Real.log_lt_log hx0 hx
  rw [Real.log_rpow hN0] at h
  rw [div_lt_iff₀ hlog]
  linarith

/-- Wu 2004 page 39, equation 10.5: replacing the finite level by the limiting argument
in a weighted prime pair sum costs `o(1)`, when the limiting arguments stay in a fixed
window `[lo, hi]` with `1 < lo` and the pair weights have bounded sum. -/
theorem pair_shift_small (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi 0)) (B lo hi : ℝ)
    (hlo : 1 < lo) (P : ℕ → Finset (ℕ × ℕ))
    (hP : ∀ N : ℕ, 2 ≤ N → ∀ q ∈ P N, q.1.Prime ∧ q.2.Prime ∧ q.1 ≠ q.2 ∧
      lo ≤ ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ∧
      ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1 ≤ hi)
    (C : ℝ) (hW : ∀ᶠ N : ℕ in atTop,
      ∑ q ∈ P N, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      |(∑ q ∈ P N, f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))) -
        ∑ q ∈ P N, f (Task348.lowerLevel B N (q.1 * q.2)) /
          (Nat.totient (q.1 * q.2) : ℝ)| ≤ ε := by
  intro ε hε
  set ε' := ε / (|C| + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hcont : ContinuousOn f (Icc (lo - 1) (hi + 1)) :=
    hf.mono fun x hx => show (0 : ℝ) < x by linarith [hx.1]
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε' hε'0
  have hsmall0 : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h1.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto
      (fun N : ℕ => 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) atTop (𝓝 0) := by
    simpa using hsmall0.const_mul (12 * B)
  have hev := (Metric.tendsto_nhds.1 hsmall) (min (δ / 2) 1) (lt_min (by linarith) one_pos)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hev.and hW)
  refine ⟨max N0 3, fun N hN => ?_⟩
  obtain ⟨hc, hWN⟩ := hN0 N (le_trans (le_max_left _ _) hN)
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  set c := 12 * B * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) with hcdef
  rw [Real.dist_eq, sub_zero] at hc
  have hc1 : |c| ≤ 1 := le_trans hc.le (min_le_right _ _)
  have hcδ : |c| < δ := lt_of_lt_of_le hc (le_trans (min_le_left _ _) (by linarith))
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ q ∈ P N,
      |f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) -
        f (Task348.lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤
        ε' * (1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))) := by
    intro q hq
    obtain ⟨hp1, hp2, hne, hlo', hhi'⟩ := hP N (by omega) q hq
    rw [totient_pair hp1 hp2 hne, lowerLevel_pair' hN3 hp1 hp2 B, ← sub_div]
    set s := ((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1
    have hw : 0 < ((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1) := by
      have a1 : (2 : ℝ) ≤ q.1 := by exact_mod_cast hp1.two_le
      have a2 : (2 : ℝ) ≤ q.2 := by exact_mod_cast hp2.two_le
      nlinarith
    rw [abs_div, abs_of_pos hw, mul_one_div]
    apply div_le_div_of_nonneg_right _ hw.le
    have hcl := abs_le.1 hc1
    have hres := hδ s ⟨by linarith, by linarith⟩ (s - c) ⟨by linarith, by linarith⟩
      (by rw [Real.dist_eq]; simpa using hcδ)
    rw [Real.dist_eq] at hres
    exact hres.le
  calc |∑ q ∈ P N, (f (((1 / 2 : ℝ) - Real.log (q.1 : ℝ) / Real.log N
          - Real.log (q.2 : ℝ) / Real.log N) / kappa1) /
            (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) -
        f (Task348.lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))|
      ≤ ∑ q ∈ P N, ε' * (1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = ε' * ∑ q ∈ P N, 1 / (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1)) := by rw [Finset.mul_sum]
    _ ≤ ε' * |C| := mul_le_mul_of_nonneg_left (hWN.trans (le_abs_self C)) hε'0.le
    _ ≤ ε := by
        rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

end LeanLab.ChenDoubleSieve.Task315.FeedS120
