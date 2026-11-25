import LeanLab.ChenDoubleSieve.Decomp349cSplitSum

/-!
Reduction of `pair_low_tendsto` and `pair_high_tendsto` in `Decomp349cSplitSum`,
Wu 2004 page 41 equation 10.12, the F9 integrals.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
With t equal log p over log N and u equal log q over log N, the refined weight
unfolds to 36/5 over 1 minus t below the one tenth cutoff and to 8 above it, and
log N over log of N over p q equals 1 over 1 minus t minus u. The domain of the
filtered `refinedPairs` lies between the open and the closed region
kappa1 to 1/10 or 1/10 to sigma1 in t, sigma1 to 1 minus t over 2 in u, apart from
primes dividing N. The inner u integral is evaluated in closed form as
log of 1/sigma1 minus 1 minus t/sigma1 over 1 minus t.
One general two variable prime Riemann sum statement, the prime partial
summation of Wu page 39 equation 10.5 for a region between continuous curves,
is left as a LEAF; everything else is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open Task275 Task348 Task349
open Wu04Functional (IsBuchstab)

/-- LEAF: Wu 2004 page 39 equation 10.5 and page 41 equation 10.12, prime partial
summation in two variables: a double sum over prime pairs with a continuous weight
of t equal log p over log N and u equal log q over log N, over a region between
two continuous curves u equal lo t and u equal hi t, tends to the double integral
of the weight against dt du over t u. The sets S N need only lie between the
closed region and the open region restricted to primes coprime to N; the boundary
and the primes dividing N carry vanishing reciprocal mass. Class HARD. -/
theorem pt_prime_region_riemann {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)})
    (S : ℕ → Finset (ℕ × ℕ))
    (hclosed : ∀ᶠ N : ℕ in atTop, ∀ q ∈ S N, q.1.Prime ∧ q.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2 : ℝ) / log N ∈ Icc (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)))
    (hopen : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ × ℕ, q.1.Prime → q.2.Prime → q.1 < N → q.2 < N →
      q.1.Coprime N → q.2.Coprime N →
      log (q.1 : ℝ) / log N ∈ Ioo a b →
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)) →
      q ∈ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  sorry

/-! ## The inner integral, Wu page 41 -/

/-- Partial fractions: the integral of 1 over u times c minus u from s to c/2 is
log of c minus s over s, divided by c. -/
theorem pt_inner_integral {c s : ℝ} (hs : 0 < s) (hsc : s ≤ c / 2) :
    ∫ u in s..c / 2, 1 / ((c - u) * u) = log ((c - s) / s) / c := by
  have hc : 0 < c := by linarith
  have key : ∀ u ∈ uIcc s (c / 2), 1 / ((c - u) * u) = (1 / c) * (u⁻¹ + (c - u)⁻¹) := by
    intro u hu
    rw [uIcc_of_le hsc] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hcu : 0 < c - u := by linarith [hu.2]
    field_simp
    ring
  have hi1 : IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume s (c / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu
    rw [uIcc_of_le hsc] at hu
    exact (by linarith [hu.1] : (0:ℝ) < u).ne'
  have hi2 : IntervalIntegrable (fun u : ℝ => (c - u)⁻¹) MeasureTheory.volume s (c / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro u hu
    rw [uIcc_of_le hsc] at hu
    exact (by linarith [hu.2] : (0:ℝ) < c - u).ne'
  have h1 : ∫ u in s..c / 2, u⁻¹ = log ((c / 2) / s) := integral_inv_of_pos hs (by linarith)
  have h2 : ∫ u in s..c / 2, (c - u)⁻¹ = log ((c - s) / (c - c / 2)) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) c (a := s) (b := c / 2)
    rw [this]
    exact integral_inv_of_pos (by linarith) (by linarith)
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi1 hi2, h1, h2,
    ← log_mul (by positivity) (by have : 0 < c - s := by linarith
                                  have : 0 < c - c / 2 := by linarith
                                  positivity)]
  rw [one_div_mul_eq_div]
  have hcc : c - c / 2 ≠ 0 := by
    have : 0 < c - c / 2 := by linarith
    exact this.ne'
  congr 2
  field_simp
  ring

/-- The inner integral of Wu page 41 in the coordinates of the F9 integrand:
for t below 1 minus 2 sigma1, the u integral from sigma1 to 1 minus t over 2 of
1 over 1 minus t minus u, times t u, is log of 1/sigma1 minus 1 minus t/sigma1
divided by t times 1 minus t. -/
theorem pt_inner_F9 {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 - 2 * sigma1) (K : ℝ) :
    ∫ u in sigma1..(1 - t) / 2, K / (1 - t - u) / (t * u) =
      K * log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)) := by
  have hs : (0 : ℝ) < sigma1 := by norm_num [sigma1]
  have hsc : sigma1 ≤ (1 - t) / 2 := by linarith
  have h := pt_inner_integral (c := 1 - t) hs hsc
  have hfun : (fun u : ℝ => K / (1 - t - u) / (t * u)) =
      fun u => (K / t) * (1 / ((1 - t - u) * u)) := by
    funext u
    simp only [div_eq_mul_inv, mul_inv, one_mul]
    ring
  rw [hfun, intervalIntegral.integral_const_mul, h]
  have h1t : (1 : ℝ) - t ≠ 0 := by
    have : (0 : ℝ) < 1 - t := by linarith
    exact this.ne'
  rw [show (1 - t - sigma1) / sigma1 = 1 / sigma1 - 1 - t / sigma1 by field_simp; ring]
  field_simp

/-! ## Coordinate translations, N at least 2 -/

theorem pt_rpow_le_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (N : ℝ) ^ σ ≤ p ↔ σ ≤ log (p : ℝ) / log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hL, rpow_def_of_pos hN0, ← le_log_iff_exp_le hp0, mul_comm]

theorem pt_lt_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) < (N : ℝ) ^ σ ↔ log (p : ℝ) / log N < σ := by
  rw [← not_le, pt_rpow_le_iff hN hp σ, not_le]

theorem pt_le_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) ≤ (N : ℝ) ^ σ ↔ log (p : ℝ) / log N ≤ σ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hL, rpow_def_of_pos hN0, ← log_le_iff_le_exp hp0, mul_comm]

theorem pt_lt_sqrt_iff {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    (q : ℝ) < sqrt ((N : ℝ) / p) ↔
      log (q : ℝ) / log N < (1 - log (p : ℝ) / log N) / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [lt_sqrt hq0.le, lt_div_iff₀ hp0, ← log_lt_log_iff (by positivity) hN0,
    log_mul (by positivity) hp0.ne', log_pow]
  rw [show (1 - log (p : ℝ) / log N) / 2 = (log N - log p) / (2 * log N) by
    field_simp]
  rw [lt_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hL]
  push_cast
  constructor <;> intro h <;> nlinarith

/-- Membership in `refinedPairs` in the coordinates t and u. -/
theorem pt_mem_refinedPairs {N : ℕ} (hN : 2 ≤ N) (q : ℕ × ℕ) :
    q ∈ refinedPairs N ↔ q.1 < N ∧ q.2 < N ∧ q.1.Prime ∧ q.2.Prime ∧
      q.1.Coprime N ∧ q.2.Coprime N ∧
      kappa1 ≤ log (q.1 : ℝ) / log N ∧ log (q.1 : ℝ) / log N < sigma1 ∧
      sigma1 ≤ log (q.2 : ℝ) / log N ∧
      log (q.2 : ℝ) / log N < (1 - log (q.1 : ℝ) / log N) / 2 := by
  unfold refinedPairs Wu08Sum.P2
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp, hq, hc1, hc2, a1, a2, a3, a4⟩
    have hp0 := hp.pos
    have hq0 := hq.pos
    exact ⟨h1, h2, hp, hq, hc1, hc2, (pt_rpow_le_iff hN hp0 _).1 a1,
      (pt_lt_rpow_iff hN hp0 _).1 a2, (pt_rpow_le_iff hN hq0 _).1 a3,
      (pt_lt_sqrt_iff hN hp0 hq0).1 a4⟩
  · rintro ⟨h1, h2, hp, hq, hc1, hc2, a1, a2, a3, a4⟩
    have hp0 := hp.pos
    have hq0 := hq.pos
    exact ⟨⟨h1, h2⟩, hp, hq, hc1, hc2, (pt_rpow_le_iff hN hp0 _).2 a1,
      (pt_lt_rpow_iff hN hp0 _).2 a2, (pt_rpow_le_iff hN hq0 _).2 a3,
      (pt_lt_sqrt_iff hN hp0 hq0).2 a4⟩

/-- The summand identity: log N over p q log of N over p q is 1 over p q times
1 minus t minus u. -/
theorem pt_summand {N : ℕ} (hN : 2 ≤ N) (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (w : ℝ) :
    log N * (w / (((p : ℝ) * q) * log ((N : ℝ) / ((p : ℝ) * q)))) =
      w / (1 - log (p : ℝ) / log N - log (q : ℝ) / log N) / ((p : ℝ) * q) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [log_div hN0.ne' (by positivity), log_mul hp0.ne' hq0.ne']
  rw [show 1 - log (p : ℝ) / log N - log (q : ℝ) / log N =
    (log N - log p - log q) / log N by field_simp]
  rw [div_div_eq_mul_div]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ## The two targets -/

/-- Statement identical to `pair_low_tendsto`, Wu 2004 page 41 equation 10.12, F9
first integral, proved from the LEAF `pt_prime_region_riemann`. -/
theorem pair_low_tendsto_proved :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedPairs N).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2))))
      atTop (𝓝 (36 / 5 * ∫ t in kappa1..(1 / 10 : ℝ),
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2))) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hab : kappa1 ≤ (1 / 10 : ℝ) := by norm_num [kappa1]
  have hs0 : (0 : ℝ) < sigma1 := by norm_num [sigma1]
  have hs1 : (1 / 10 : ℝ) < sigma1 := by norm_num [sigma1]
  have hst : (1 / 10 : ℝ) ≤ 1 - 2 * sigma1 := by norm_num [sigma1]
  let g : ℝ × ℝ → ℝ := fun x => 36 / 5 / (1 - x.1) / (1 - x.1 - x.2)
  have hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc kappa1 (1 / 10) ∧
      x.2 ∈ Icc ((fun _ => sigma1) x.1) ((fun t : ℝ => (1 - t) / 2) x.1)} := by
    apply ContinuousOn.div
    · apply ContinuousOn.div continuousOn_const
      · exact (continuousOn_const.sub continuous_fst.continuousOn)
      · intro x hx
        have := hx.1.2
        linarith
    · exact (continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn
    · intro x hx
      have h1 := hx.1.2
      have h2 := hx.2.2
      try simp only at h1 h2
      linarith
  have hR := pt_prime_region_riemann (a := kappa1) (b := 1 / 10) (lo := fun _ => sigma1)
    (hi := fun t => (1 - t) / 2) (g := g) hk hab (by norm_num) continuousOn_const
    ((continuousOn_const.sub continuousOn_id).div_const 2)
    (fun _ _ => hs0) (fun t ht => by linarith [ht.2])
    (fun t ht => by linarith [ht.1]) hg
    (fun N => (refinedPairs N).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, pt_mem_refinedPairs hN] at hq
      obtain ⟨⟨_, _, hp, hq', _, _, a1, _, a3, a4⟩, h10⟩ := hq
      exact ⟨hp, hq', ⟨a1, (pt_le_rpow_iff hN hp.pos _).1 h10⟩, ⟨a3, a4.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp hq h1 h2 hc1 hc2 ht hu
      rw [Finset.mem_filter, pt_mem_refinedPairs hN]
      exact ⟨⟨h1, h2, hp, hq, hc1, hc2, ht.1.le, by linarith [ht.2], hu.1.le, hu.2⟩,
        (pt_le_rpow_iff hN hp.pos _).2 ht.2.le⟩)
  have hI : (∫ t in kappa1..(1 / 10 : ℝ), ∫ u in (fun _ => sigma1) t..(fun t : ℝ => (1 - t) / 2) t,
      g (t, u) / (t * u)) = 36 / 5 * ∫ t in kappa1..(1 / 10 : ℝ),
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : (1 : ℝ) - t ≠ 0 := by
      have : (0 : ℝ) < 1 - t := by linarith [ht.2]
      exact this.ne'
    simp only [g]
    rw [pt_inner_F9 ht0 (by linarith [ht.2])]
    field_simp
  rw [hI] at hR
  refine hR.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq2 := hq
  rw [Finset.mem_filter, pt_mem_refinedPairs hN] at hq2
  obtain ⟨⟨_, _, hp, hq', _⟩, h10⟩ := hq2
  unfold refinedWeight
  rw [if_pos h10, pt_summand hN _ _ hp.pos hq'.pos]

/-- Statement identical to `pair_high_tendsto`, Wu 2004 page 41 equation 10.12, F9
second integral, proved from the LEAF `pt_prime_region_riemann`. -/
theorem pair_high_tendsto_proved :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedPairs N).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2))))
      atTop (𝓝 (8 * ∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)))) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk10 : kappa1 < (1 / 10 : ℝ) := by norm_num [kappa1]
  have hs0 : (0 : ℝ) < sigma1 := by norm_num [sigma1]
  have hs1 : (1 / 10 : ℝ) ≤ sigma1 := by norm_num [sigma1]
  have hst : sigma1 ≤ 1 - 2 * sigma1 := by norm_num [sigma1]
  let g : ℝ × ℝ → ℝ := fun x => 8 / (1 - x.1 - x.2)
  have hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc (1 / 10) sigma1 ∧
      x.2 ∈ Icc ((fun _ => sigma1) x.1) ((fun t : ℝ => (1 - t) / 2) x.1)} := by
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_const.sub continuous_fst.continuousOn).sub continuous_snd.continuousOn
    · intro x hx
      have h1 := hx.1.2
      have h2 := hx.2.2
      try simp only at h1 h2
      linarith
  have hR := pt_prime_region_riemann (a := 1 / 10) (b := sigma1) (lo := fun _ => sigma1)
    (hi := fun t => (1 - t) / 2) (g := g) (by norm_num) hs1 (by norm_num [sigma1])
    continuousOn_const ((continuousOn_const.sub continuousOn_id).div_const 2)
    (fun _ _ => hs0) (fun t ht => by linarith [ht.2])
    (fun t ht => by linarith [ht.1]) hg
    (fun N => (refinedPairs N).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, pt_mem_refinedPairs hN] at hq
      obtain ⟨⟨_, _, hp, hq', _, _, _, a2, a3, a4⟩, h10⟩ := hq
      rw [pt_le_rpow_iff hN hp.pos, not_le] at h10
      exact ⟨hp, hq', ⟨h10.le, a2.le⟩, ⟨a3, a4.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp hq h1 h2 hc1 hc2 ht hu
      rw [Finset.mem_filter, pt_mem_refinedPairs hN, pt_le_rpow_iff hN hp.pos, not_le]
      exact ⟨⟨h1, h2, hp, hq, hc1, hc2, by linarith [ht.1], ht.2, hu.1.le, hu.2⟩, ht.1⟩)
  have hI : (∫ t in (1 / 10 : ℝ)..sigma1, ∫ u in (fun _ => sigma1) t..(fun t : ℝ => (1 - t) / 2) t,
      g (t, u) / (t * u)) = 8 * ∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs1] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    simp only [g]
    rw [pt_inner_F9 ht0 (by linarith [ht.2])]
    ring
  rw [hI] at hR
  refine hR.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq2 := hq
  rw [Finset.mem_filter, pt_mem_refinedPairs hN] at hq2
  obtain ⟨⟨_, _, hp, hq', _⟩, h10⟩ := hq2
  unfold refinedWeight
  rw [if_neg h10, pt_summand hN _ _ hp.pos hq'.pos]


end LeanLab.ChenDoubleSieve.Task349.SplitSum
