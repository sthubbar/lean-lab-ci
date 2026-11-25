import LeanLab.ChenDoubleSieve.Decomp349bSplitSum

/-!
Reduction of `leaf_free_sum_tendsto` in `Decomp349bSplitSum`, Wu 2004 page 41,
display 10.9 and its analogue 10.11. Source: https://arxiv.org/pdf/0705.1652.
After multiplication by log N the summand of `freeSum` is a continuous weight of
the coordinates t equal log p over log N and u equal log q over log N, divided by
p q. The domain of `freePairs` is sandwiched between the open and the closed
region of the t u plane. One general two variable prime Riemann sum lemma, the
prime partial summation of Wu page 39 equation 10.5 for moving regions, is left
as a LEAF; everything else is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 39 equation 10.5 and page 41 display 10.9, the standard
replacement of a double sum over primes by a double integral by prime partial
summation, for a region between two continuous curves u equal lo t and u equal
hi t over a band of t. Any family of prime pair sets lying eventually between the
open and the closed region has the double integral as the limit of its reciprocal
weighted sum, since the boundary pairs carry mass at most 2 times N to the minus
min lo times the bounded outer prime mass. Class HARD. -/
theorem leaf_prime_region_riemann {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
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
      log (q.1 : ℝ) / log N ∈ Ioo a b →
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)) →
      q ∈ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  sorry

/-! ## Coordinate translations, N at least 2 -/

theorem fs_rpow_le_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (N : ℝ) ^ σ ≤ p ↔ σ ≤ log (p : ℝ) / log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hL, rpow_def_of_pos hN0, ← le_log_iff_exp_le hp0, mul_comm]

theorem fs_lt_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) < (N : ℝ) ^ σ ↔ log (p : ℝ) / log N < σ := by
  rw [← not_le, fs_rpow_le_iff hN hp σ, not_le]

theorem fs_lt_iff {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    p < q ↔ log (p : ℝ) / log N < log (q : ℝ) / log N := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_lt_div_iff_of_pos_right hL, log_lt_log_iff hp0 hq0]
  exact Nat.cast_lt.symm

theorem fs_lt_sqrt_iff {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    (q : ℝ) < sqrt ((N : ℝ) / p) ↔
      log (q : ℝ) / log N < (1 - log (p : ℝ) / log N) / 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (q : ℝ) < sqrt ((N : ℝ) / p) ↔ 2 * log (q : ℝ) + log p < log N := by
    rw [lt_sqrt hq0.le, lt_div_iff₀ hp0, ← log_lt_log_iff (by positivity) hN0,
      log_mul (by positivity) hp0.ne', log_pow]
    push_cast
    exact Iff.rfl
  rw [h1]
  have hx : log (q : ℝ) = log q / log N * log N := by field_simp
  have hy : log (p : ℝ) = log p / log N * log N := by field_simp
  set x := log (q : ℝ) / log N
  set y := log (p : ℝ) / log N
  rw [hx, hy]
  constructor <;> intro h <;> nlinarith

/-- The summand of `freeSum` times log N, in the coordinates of Wu page 41. -/
theorem fs_summand {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    log (N : ℝ) * (1 / (((p : ℝ) * q) * log ((N : ℝ) / ((p : ℝ) * q)))) =
      (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2))
        (log (p : ℝ) / log N, log (q : ℝ) / log N) / ((p : ℝ) * q) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  simp only
  rw [log_div hN0.ne' (by positivity), log_mul hp0.ne' hq0.ne']
  have he : 1 - log (p : ℝ) / log N - log (q : ℝ) / log N =
      (log N - log p - log q) / log N := by field_simp
  rw [he, sub_add_eq_sub_sub, one_div_div]
  generalize log (N : ℝ) - log p - log q = D
  ring

/-- The integrand of `switchedIntegral` is the weight divided by t u. -/
theorem fs_integrand (t u : ℝ) :
    1 / (t * u * (1 - t - u)) = (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2)) (t, u) / (t * u) := by
  simp only
  rw [div_div, mul_comm (1 - t - u)]

theorem fs_weight_continuous {a b : ℝ} {lo hi : ℝ → ℝ}
    (hb : b ≤ 1 / 3) (hhi : ∀ t ∈ Icc a b, hi t ≤ (1 - t) / 2) :
    ContinuousOn (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2))
      {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)} := by
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  rintro x ⟨h1, h2⟩
  have := hhi x.1 h1
  have := h1.2
  have := h2.2
  linarith

/-- `leaf_free_sum_tendsto`, exactly as stated in `Decomp349bSplitSum`, proved from
`leaf_prime_region_riemann`. CONDITIONAL ON that LEAF. -/
theorem leaf_free_sum_tendsto_proved :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * freeSum N i) atTop
        (𝓝 (8 * switchedIntegral i)) := by
  intro i hi
  have hev2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have key : Tendsto (fun N : ℕ => log N * freeSum N i) atTop (𝓝 (switchedIntegral i)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · -- i = 6, Wu display 10.9 with lower endpoint sigma one
      have hσ : (0 : ℝ) < sigma1 := by norm_num [sigma1]
      have hσ3 : sigma1 ≤ 1 / 3 := by norm_num [sigma1]
      have L := leaf_prime_region_riemann (a := sigma1) (b := 1 / 3) (lo := fun t => t)
        (hi := fun t => (1 - t) / 2) (g := fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2))
        hσ hσ3 (by norm_num) continuousOn_id (by fun_prop)
        (fun t ht => by have := ht.1; (try simp only); linarith)
        (fun t ht => by have := ht.2; (try simp only); linarith)
        (fun t ht => by have := ht.1; (try simp only); linarith)
        (fs_weight_continuous (a := sigma1) (b := 1 / 3) (lo := fun t => t) (by norm_num) (fun t _ => le_rfl))
        (fun N => freePairs N 6)
        (by
          filter_upwards [hev2] with N hN q hq
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
          obtain ⟨-, hp1, hp2, hlow, hpq, hsq⟩ := hq
          have h0 := hp1.pos
          have h0' := hp2.pos
          rw [fs_rpow_le_iff hN h0] at hlow
          rw [fs_lt_iff hN h0 h0'] at hpq
          rw [fs_lt_sqrt_iff hN h0 h0'] at hsq
          refine ⟨hp1, hp2, ⟨hlow, by linarith⟩, hpq.le, hsq.le⟩)
        (by
          filter_upwards [hev2] with N hN q hp1 hp2 hpN hqN ht hu
          have h0 := hp1.pos
          have h0' := hp2.pos
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          refine ⟨⟨hpN, hqN⟩, hp1, hp2, (fs_rpow_le_iff hN h0 _).2 ht.1.le,
            (fs_lt_iff hN h0 h0').2 hu.1, (fs_lt_sqrt_iff hN h0 h0').2 hu.2⟩)
      have E : switchedIntegral 6 = ∫ t in sigma1..(1 / 3 : ℝ), ∫ u in (fun t : ℝ => t) t..(fun t : ℝ => (1 - t) / 2) t,
          (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2)) (t, u) / (t * u) := by
        rw [switchedIntegral, if_neg (by decide), if_pos rfl]
        simp only [fs_integrand]
      rw [E]
      refine L.congr' ?_
      · filter_upwards [hev2] with N hN
        try dsimp only
        rw [freeSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        simp only [freePairs, Finset.mem_filter] at hq
        exact (fs_summand hN hq.2.1.pos hq.2.2.1.pos).symm
    · -- i = 7, Wu display 10.9 with lower endpoint sigma two
      have hσ : (0 : ℝ) < sigma2 := by norm_num [sigma2]
      have hσ3 : sigma2 ≤ 1 / 3 := by norm_num [sigma2]
      have L := leaf_prime_region_riemann (a := sigma2) (b := 1 / 3) (lo := fun t => t)
        (hi := fun t => (1 - t) / 2) (g := fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2))
        hσ hσ3 (by norm_num) continuousOn_id (by fun_prop)
        (fun t ht => by have := ht.1; (try simp only); linarith)
        (fun t ht => by have := ht.2; (try simp only); linarith)
        (fun t ht => by have := ht.1; (try simp only); linarith)
        (fs_weight_continuous (a := sigma2) (b := 1 / 3) (lo := fun t => t) (by norm_num) (fun t _ => le_rfl))
        (fun N => freePairs N 7)
        (by
          filter_upwards [hev2] with N hN q hq
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            if_neg (by decide : (7 : Fin 12) ≠ 6)] at hq
          obtain ⟨-, hp1, hp2, hlow, hpq, hsq⟩ := hq
          have h0 := hp1.pos
          have h0' := hp2.pos
          rw [fs_rpow_le_iff hN h0] at hlow
          rw [fs_lt_iff hN h0 h0'] at hpq
          rw [fs_lt_sqrt_iff hN h0 h0'] at hsq
          refine ⟨hp1, hp2, ⟨hlow, by linarith⟩, hpq.le, hsq.le⟩)
        (by
          filter_upwards [hev2] with N hN q hp1 hp2 hpN hqN ht hu
          have h0 := hp1.pos
          have h0' := hp2.pos
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            if_neg (by decide : (7 : Fin 12) ≠ 6)]
          refine ⟨⟨hpN, hqN⟩, hp1, hp2, (fs_rpow_le_iff hN h0 _).2 ht.1.le,
            (fs_lt_iff hN h0 h0').2 hu.1, (fs_lt_sqrt_iff hN h0 h0').2 hu.2⟩)
      have E : switchedIntegral 7 = ∫ t in sigma2..(1 / 3 : ℝ), ∫ u in (fun t : ℝ => t) t..(fun t : ℝ => (1 - t) / 2) t,
          (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2)) (t, u) / (t * u) := by
        rw [switchedIntegral, if_neg (by decide), if_neg (by decide)]
        simp only [fs_integrand]
      rw [E]
      refine L.congr' ?_
      · filter_upwards [hev2] with N hN
        try dsimp only
        rw [freeSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        simp only [freePairs, Finset.mem_filter] at hq
        exact (fs_summand hN hq.2.1.pos hq.2.2.1.pos).symm
    · -- i = 9, Wu display 10.11
      have hk : (0 : ℝ) < kappa2 := by norm_num [kappa2]
      have hks : kappa2 ≤ sigma2 := by norm_num [kappa2, sigma2]
      have L := leaf_prime_region_riemann (a := kappa2) (b := sigma2) (lo := fun _ => sigma2)
        (hi := fun t => (1 - t) / 2) (g := fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2))
        hk hks (by norm_num [sigma2]) continuousOn_const (by fun_prop)
        (fun t ht => by norm_num [sigma2])
        (fun t ht => by have := ht.2; norm_num [sigma2] at this ⊢; linarith)
        (fun t ht => by have := ht.1; (try simp only); linarith)
        (fs_weight_continuous (a := kappa2) (b := sigma2) (lo := fun _ => sigma2) (by norm_num [sigma2])
          (fun t _ => le_rfl))
        (fun N => freePairs N 9)
        (by
          filter_upwards [hev2] with N hN q hq
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            if_neg (by decide : (9 : Fin 12) ≠ 6), if_neg (by decide : (9 : Fin 12) ≠ 7)] at hq
          obtain ⟨-, hp1, hp2, ⟨hlow, hup, hq2⟩, -, hsq⟩ := hq
          have h0 := hp1.pos
          have h0' := hp2.pos
          rw [fs_rpow_le_iff hN h0] at hlow
          rw [fs_lt_rpow_iff hN h0] at hup
          rw [fs_rpow_le_iff hN h0'] at hq2
          rw [fs_lt_sqrt_iff hN h0 h0'] at hsq
          exact ⟨hp1, hp2, ⟨hlow, hup.le⟩, hq2, hsq.le⟩)
        (by
          filter_upwards [hev2] with N hN q hp1 hp2 hpN hqN ht hu
          have h0 := hp1.pos
          have h0' := hp2.pos
          simp only [freePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
            if_neg (by decide : (9 : Fin 12) ≠ 6), if_neg (by decide : (9 : Fin 12) ≠ 7)]
          refine ⟨⟨hpN, hqN⟩, hp1, hp2, ⟨(fs_rpow_le_iff hN h0 _).2 ht.1.le,
            (fs_lt_rpow_iff hN h0 _).2 ht.2, (fs_rpow_le_iff hN h0' _).2 hu.1.le⟩,
            (fs_lt_iff hN h0 h0').2 (ht.2.trans hu.1), (fs_lt_sqrt_iff hN h0 h0').2 hu.2⟩)
      have E : switchedIntegral 9 = ∫ t in kappa2..sigma2, ∫ u in (fun _ : ℝ => sigma2) t..(fun t : ℝ => (1 - t) / 2) t,
          (fun x : ℝ × ℝ => 1 / (1 - x.1 - x.2)) (t, u) / (t * u) := by
        rw [switchedIntegral, if_pos rfl]
        simp only [fs_integrand]
      rw [E]
      refine L.congr' ?_
      · filter_upwards [hev2] with N hN
        try dsimp only
        rw [freeSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        simp only [freePairs, Finset.mem_filter] at hq
        exact (fs_summand hN hq.2.1.pos hq.2.2.1.pos).symm
  have h8 := key.const_mul 8
  refine h8.congr' (Eventually.of_forall fun N => ?_)
  ring

end LeanLab.ChenDoubleSieve.Task349
