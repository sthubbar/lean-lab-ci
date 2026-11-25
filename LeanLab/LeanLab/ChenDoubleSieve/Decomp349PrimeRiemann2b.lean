import LeanLab.ChenDoubleSieve.Decomp349PrimeRiemann2

/-!
Split of the LEAF `prc_boundary_weighted` of `Decomp349PrimeRiemann2`, Wu 2004
arXiv 0705.1652 page 39 equation 10.5, the boundary step of the prime pair Riemann sums.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
The weight g is bounded on the compact region, so the weighted boundary mass is at most
a constant times the reciprocal mass of the pairs in the closed region set but not in
the open region set. Those pairs have the first coordinate on the boundary t equal a or
b or a first prime dividing N, or the second coordinate on a boundary curve or a second
prime dividing N. Both coordinate bounds are proved, so the weighted boundary step
is proved in full.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.PrimeRiemannCore

/-- The closed region between two continuous curves is compact. -/
theorem prc_region_isCompact {a b : ℝ} {lo hi : ℝ → ℝ}
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1) :
    IsCompact {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)} := by
  have hs : IsClosed (Icc a b ×ˢ (univ : Set ℝ)) := isClosed_Icc.prod isClosed_univ
  have hf : ContinuousOn (fun x : ℝ × ℝ => (lo x.1, x.2, hi x.1)) (Icc a b ×ˢ univ) := by
    have h1 : ContinuousOn (fun x : ℝ × ℝ => lo x.1) (Icc a b ×ˢ univ) :=
      hlo.comp continuousOn_fst (fun x hx => hx.1)
    have h2 : ContinuousOn (fun x : ℝ × ℝ => hi x.1) (Icc a b ×ˢ univ) :=
      hhi.comp continuousOn_fst (fun x hx => hx.1)
    exact h1.prodMk (continuousOn_snd.prodMk h2)
  have ht : IsClosed {y : ℝ × ℝ × ℝ | y.1 ≤ y.2.1 ∧ y.2.1 ≤ y.2.2} :=
    (isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
      (isClosed_le (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))
  have hcl := hf.preimage_isClosed_of_isClosed hs ht
  refine ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
  · convert hcl using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
      Set.mem_preimage, Set.mem_Icc]
  · intro x hx
    refine ⟨hx.1, ?_, ?_⟩
    · exact (hlo0 _ hx.1).le.trans hx.2.1
    · exact hx.2.2.trans (hhi1 _ hx.1)

/-- Wu 2004 page 39, divisor count: distinct primes dividing N, each at least N to the a,
number at most 1 / a, since their product divides N. -/
theorem prc_card_dvd_bound {N : ℕ} {a : ℝ} (ha : 0 < a) (hN : 2 ≤ N) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ∣ N ∧ (N : ℝ) ^ a ≤ p) : (s.card : ℝ) ≤ 1 / a := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdvd : (∏ p ∈ s, p) ∣ N :=
    Finset.prod_primes_dvd N (fun p hp => (hs p hp).1.prime) (fun p hp => (hs p hp).2.1)
  have hle : (∏ p ∈ s, p) ≤ N := Nat.le_of_dvd (by omega) hdvd
  have h1 : ((N : ℝ) ^ a) ^ s.card ≤ ∏ p ∈ s, (p : ℝ) := by
    rw [← Finset.prod_const]
    gcongr with p hp
    exact (hs p hp).2.2
  have h2 : ∏ p ∈ s, (p : ℝ) ≤ N := by rw [← Nat.cast_prod]; exact_mod_cast hle
  have h3 : ((N : ℝ) ^ a) ^ s.card ≤ N := h1.trans h2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le] at h3
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_rpow hN0] at h4
  have h5 : a * s.card ≤ 1 := (mul_le_iff_le_one_left hL).mp h4
  rw [le_div_iff₀ ha]
  linarith

/-- At most one positive integer has log p / log N equal to a given level c. -/
theorem prc_card_level_le_one {N : ℕ} (hN : 2 ≤ N) (c : ℝ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 0 < p ∧ log (p : ℝ) / log N = c) : s.card ≤ 1 := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  refine Finset.card_le_one.2 fun x hx y hy => ?_
  obtain ⟨x0, hx1⟩ := hs x hx
  obtain ⟨y0, hy1⟩ := hs y hy
  have hxy : log (x : ℝ) = log (y : ℝ) := by
    rw [← hy1, div_left_inj' hL.ne'] at hx1; exact hx1
  have := Real.log_injOn_pos (Set.mem_Ioi.2 (by exact_mod_cast x0 : (0 : ℝ) < x))
    (Set.mem_Ioi.2 (by exact_mod_cast y0 : (0 : ℝ) < y)) hxy
  exact_mod_cast this

/-- Reciprocal mass of a set of primes at least N to the c, each on one of two levels or
dividing N: at most 3 + 1 / c times N to the minus c. -/
theorem prc_level_sum_bound {N : ℕ} (hN : 2 ≤ N) {c c1 c2 : ℝ} (hc : 0 < c) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ (N : ℝ) ^ c ≤ r ∧
      (log (r : ℝ) / log N = c1 ∨ log (r : ℝ) / log N = c2 ∨ r ∣ N)) :
    ∑ r ∈ R, 1 / (r : ℝ) ≤ (3 + 1 / c) * ((N : ℝ) ^ c)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsplit : R ⊆ R.filter (fun r : ℕ => log (r : ℝ) / log N = c1) ∪
      R.filter (fun r : ℕ => log (r : ℝ) / log N = c2) ∪ R.filter (fun r : ℕ => r ∣ N) := by
    intro r hr
    rcases (hR r hr).2.2 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hr, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hr, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hr, h⟩)
  have c1' := prc_card_level_le_one hN c1 (R.filter (fun r : ℕ => log (r : ℝ) / log N = c1))
    (fun r hr => ⟨(hR r (Finset.mem_filter.1 hr).1).1.pos, (Finset.mem_filter.1 hr).2⟩)
  have c2' := prc_card_level_le_one hN c2 (R.filter (fun r : ℕ => log (r : ℝ) / log N = c2))
    (fun r hr => ⟨(hR r (Finset.mem_filter.1 hr).1).1.pos, (Finset.mem_filter.1 hr).2⟩)
  have c3 := prc_card_dvd_bound hc hN (R.filter (fun r : ℕ => r ∣ N))
    (fun r hr => ⟨(hR r (Finset.mem_filter.1 hr).1).1, (Finset.mem_filter.1 hr).2,
      (hR r (Finset.mem_filter.1 hr).1).2.1⟩)
  have hc := (Finset.card_le_card hsplit).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : (R.card : ℝ) ≤ ((R.filter (fun r : ℕ => log (r : ℝ) / log N = c1)).card : ℝ) +
      ((R.filter (fun r : ℕ => log (r : ℝ) / log N = c2)).card : ℝ) +
      ((R.filter (fun r : ℕ => r ∣ N)).card : ℝ) := by exact_mod_cast hc
  have c1'' : ((R.filter (fun r : ℕ => log (r : ℝ) / log N = c1)).card : ℝ) ≤ 1 := by
    exact_mod_cast c1'
  have c2'' : ((R.filter (fun r : ℕ => log (r : ℝ) / log N = c2)).card : ℝ) ≤ 1 := by
    exact_mod_cast c2'
  have hcard : (R.card : ℝ) ≤ 3 + 1 / c := by linarith
  have hy : (0 : ℝ) < (N : ℝ) ^ c := rpow_pos_of_pos hN0 c
  calc ∑ r ∈ R, 1 / (r : ℝ) ≤ ∑ _r ∈ R, ((N : ℝ) ^ c)⁻¹ := by
        refine Finset.sum_le_sum fun r hr => ?_
        rw [one_div]
        exact inv_anti₀ hy (hR r hr).2.1
    _ = R.card * ((N : ℝ) ^ c)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 + 1 / c) * ((N : ℝ) ^ c)⁻¹ := mul_le_mul_of_nonneg_right hcard (inv_nonneg.2 hy.le)

/-- Wu 2004 page 39 equation 10.5, boundary mass in the first coordinate: given
the Mertens interval limit, the reciprocal mass of the pairs of the closed region set
with t equal a or b, or with the first prime dividing N, tends to zero. At most two
primes sit on t equal a or b, at most 1 / a primes at least N to the a divide N, each
has 1 / p at most N to the minus a, and the second coordinate carries a bounded Mertens
mass. PROVED, CLOUD S132. -/
theorem prc_boundary_first {a b : ℝ} {lo hi : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ (prcClosed a b lo hi N).filter
      (fun q => log (q.1 : ℝ) / log N = a ∨ log (q.1 : ℝ) / log N = b ∨ q.1 ∣ N), 1 / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hlo
  have hm : 0 < lo t0 := hlo0 t0 ht0
  have hm1 : lo t0 ≤ 1 := (hlohi t0 ht0).trans (hhi1 t0 ht0)
  have hQ := hM (lo t0) 1 hm hm1 le_rfl
  have hpow : Tendsto (fun N : ℕ => (3 + 1 / a) * ((N : ℝ) ^ a)⁻¹) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa using h.const_mul (3 + 1 / a)
  have hprod := hpow.mul hQ
  rw [zero_mul] at hprod
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity)
    ?_ hprod
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set P0 := (Finset.range (N + 1)).filter
    (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc a b) with hP0
  set P := P0.filter (fun p : ℕ => log (p : ℝ) / log N = a ∨ log (p : ℝ) / log N = b ∨ p ∣ N)
    with hP
  set Q := (Finset.range (N + 1)).filter
    (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc (lo t0) 1) with hQd
  have hsub : (prcClosed a b lo hi N).filter (fun q => log (q.1 : ℝ) / log N = a ∨ log (q.1 : ℝ) / log N = b ∨ q.1 ∣ N) ⊆ P ×ˢ Q := by
    intro q hq
    simp only [prcClosed, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨⟨⟨r1, r2⟩, p1, p2, ht, hu⟩, e⟩ := hq
    simp only [P, P0, Q, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨r1, p1, ht⟩, e⟩, r2, p2, (hmin ht).trans hu.1, hu.2.trans (hhi1 _ ht)⟩
  have hPmem : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ a ≤ p := by
    intro p hp
    simp only [P, P0, Finset.mem_filter] at hp
    exact ⟨hp.1.2.1, (prc_rpow_le_iff hN hp.1.2.1.pos a).2 hp.1.2.2.1⟩
  have hcard : (P.card : ℝ) ≤ 3 + 1 / a := by
    have hsplit : P ⊆ P.filter (fun p : ℕ => log (p : ℝ) / log N = a) ∪
        P.filter (fun p : ℕ => log (p : ℝ) / log N = b) ∪ P.filter (fun p : ℕ => p ∣ N) := by
      intro p hp
      have hp' := hp
      simp only [P, Finset.mem_filter] at hp'
      rcases hp'.2 with h | h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hp, h⟩)
    have c1 := prc_card_level_le_one hN a (P.filter (fun p : ℕ => log (p : ℝ) / log N = a))
      (fun p hp => ⟨(hPmem p (Finset.mem_filter.1 hp).1).1.pos, (Finset.mem_filter.1 hp).2⟩)
    have c2 := prc_card_level_le_one hN b (P.filter (fun p : ℕ => log (p : ℝ) / log N = b))
      (fun p hp => ⟨(hPmem p (Finset.mem_filter.1 hp).1).1.pos, (Finset.mem_filter.1 hp).2⟩)
    have c3 := prc_card_dvd_bound ha hN (P.filter (fun p : ℕ => p ∣ N))
      (fun p hp => ⟨(hPmem p (Finset.mem_filter.1 hp).1).1, (Finset.mem_filter.1 hp).2,
        (hPmem p (Finset.mem_filter.1 hp).1).2⟩)
    have hc := (Finset.card_le_card hsplit).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have hc' : (P.card : ℝ) ≤ ((P.filter (fun p : ℕ => log (p : ℝ) / log N = a)).card : ℝ) +
        ((P.filter (fun p : ℕ => log (p : ℝ) / log N = b)).card : ℝ) +
        ((P.filter (fun p : ℕ => p ∣ N)).card : ℝ) := by exact_mod_cast hc
    have c1' : ((P.filter (fun p : ℕ => log (p : ℝ) / log N = a)).card : ℝ) ≤ 1 := by
      exact_mod_cast c1
    have c2' : ((P.filter (fun p : ℕ => log (p : ℝ) / log N = b)).card : ℝ) ≤ 1 := by
      exact_mod_cast c2
    linarith
  have hPsum : ∑ p ∈ P, 1 / (p : ℝ) ≤ (3 + 1 / a) * ((N : ℝ) ^ a)⁻¹ := by
    have hy : (0 : ℝ) < (N : ℝ) ^ a := rpow_pos_of_pos hN0 a
    calc ∑ p ∈ P, 1 / (p : ℝ) ≤ ∑ _p ∈ P, ((N : ℝ) ^ a)⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [one_div]
          exact inv_anti₀ hy (hPmem p hp).2
      _ = P.card * ((N : ℝ) ^ a)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 + 1 / a) * ((N : ℝ) ^ a)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (inv_nonneg.2 hy.le)
  have hQnn : 0 ≤ prcMertens (lo t0) 1 N := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ q ∈ (prcClosed a b lo hi N).filter (fun q => log (q.1 : ℝ) / log N = a ∨ log (q.1 : ℝ) / log N = b ∨ q.1 ∣ N),
        1 / ((q.1 : ℝ) * q.2)
      ≤ ∑ q ∈ P ×ˢ Q, 1 / ((q.1 : ℝ) * q.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (∑ p ∈ P, 1 / (p : ℝ)) * prcMertens (lo t0) 1 N := by
        rw [Finset.sum_product, prcMertens, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
        rw [one_div_mul_one_div]
    _ ≤ (3 + 1 / a) * ((N : ℝ) ^ a)⁻¹ * prcMertens (lo t0) 1 N :=
        mul_le_mul_of_nonneg_right hPsum hQnn

/-- Wu 2004 page 39 equation 10.5, boundary mass in the second coordinate: given
the Mertens interval limit, the reciprocal mass of the pairs of the closed region set
with u equal lo t or hi t, or with the second prime dividing N, tends to zero. For each
first prime at most two second primes sit on the curves and at most 1 / m second primes
at least N to the m divide N, m the minimum of lo, each with 1 / q at most N to the
minus m, and the first coordinate carries a bounded Mertens mass. PROVED, CLOUD S132. -/
theorem prc_boundary_second {a b : ℝ} {lo hi : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ (prcClosed a b lo hi N).filter
      (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N),
      1 / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hab) hlo
  have hm : 0 < lo t0 := hlo0 t0 ht0
  have hA := hM a b ha hab hb1
  have hpow : Tendsto (fun N : ℕ => (3 + 1 / lo t0) * ((N : ℝ) ^ lo t0)⁻¹) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_atTop hm).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa using h.const_mul (3 + 1 / lo t0)
  have hprod := hpow.mul hA
  rw [zero_mul] at hprod
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity)
    ?_ hprod
  filter_upwards [eventually_ge_atTop 2] with N hN
  set K := (3 + 1 / lo t0) * ((N : ℝ) ^ lo t0)⁻¹ with hK
  set P0 := (Finset.range (N + 1)).filter
    (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc a b) with hP0
  set Q := (Finset.range (N + 1)).filter
    (fun p : ℕ => p.Prime ∧ log (p : ℝ) / log N ∈ Icc (lo t0) 1) with hQd
  have hsub : (prcClosed a b lo hi N).filter
      (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N) ⊆
      (P0 ×ˢ Q).filter (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N) := by
    intro q hq
    simp only [prcClosed, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨⟨⟨r1, r2⟩, p1, p2, ht, hu⟩, e⟩ := hq
    simp only [P0, Q, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨r1, p1, ht⟩, r2, p2, (hmin ht).trans hu.1, hu.2.trans (hhi1 _ ht)⟩, e⟩
  have inner : ∀ p ∈ P0, ∑ r ∈ Q.filter (fun r : ℕ => log (r : ℝ) / log N =
      lo (log (p : ℝ) / log N) ∨ log (r : ℝ) / log N = hi (log (p : ℝ) / log N) ∨ r ∣ N),
      1 / (r : ℝ) ≤ K := by
    intro p _
    refine prc_level_sum_bound hN (c1 := lo (log (p : ℝ) / log N)) (c2 := hi (log (p : ℝ) / log N))
      hm _ fun r hr => ?_
    simp only [Q, Finset.mem_filter, Finset.mem_range] at hr
    exact ⟨hr.1.2.1, (prc_rpow_le_iff hN hr.1.2.1.pos _).2 hr.1.2.2.1, hr.2⟩
  have hAnn : 0 ≤ prcMertens a b N := Finset.sum_nonneg fun _ _ => by positivity
  calc ∑ q ∈ (prcClosed a b lo hi N).filter
        (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N), 1 / ((q.1 : ℝ) * q.2)
      ≤ ∑ q ∈ (P0 ×ˢ Q).filter (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N),
        1 / ((q.1 : ℝ) * q.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ p ∈ P0, 1 / (p : ℝ) * ∑ r ∈ Q.filter (fun r : ℕ => log (r : ℝ) / log N =
        lo (log (p : ℝ) / log N) ∨ log (r : ℝ) / log N = hi (log (p : ℝ) / log N) ∨ r ∣ N),
        1 / (r : ℝ) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter (s := Q)]
        refine Finset.sum_congr rfl fun r _ => ?_
        exact if_congr Iff.rfl (one_div_mul_one_div _ _).symm rfl
    _ ≤ ∑ p ∈ P0, 1 / (p : ℝ) * K :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (inner p hp) (by positivity)
    _ = K * prcMertens a b N := by rw [← Finset.sum_mul, prcMertens, mul_comm]

/-- Wu 2004 page 39 equation 10.5, the reciprocal boundary mass: the pairs of the closed
region set outside the open region set have reciprocal mass tending to zero, from the
proved `prc_boundary_first` and `prc_boundary_second`. -/
theorem prc_boundary_mass {a b : ℝ} {lo hi : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ prcClosed a b lo hi N \ prcOpen a b lo hi N,
      1 / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
  have h1 := prc_boundary_first ha hab hb1 hlo hhi hlo0 hlohi hhi1 hM
  have h2 := prc_boundary_second ha hab hb1 hlo hhi hlo0 hlohi hhi1 hM
  have h12 := h1.add h2
  rw [add_zero] at h12
  refine squeeze_zero' (Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity)
    ?_ h12
  filter_upwards with N
  have hsub : prcClosed a b lo hi N \ prcOpen a b lo hi N ⊆
      (prcClosed a b lo hi N).filter (fun q => log (q.1 : ℝ) / log N = a ∨ log (q.1 : ℝ) / log N = b ∨ q.1 ∣ N) ∪
      (prcClosed a b lo hi N).filter (fun q => log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N) := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    obtain ⟨hC, hO⟩ := hq
    have hC' := hC
    simp only [prcClosed, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hC'
    obtain ⟨⟨r1, r2⟩, p1, p2, ht, hu⟩ := hC'
    by_cases e1 : log (q.1 : ℝ) / log N = a ∨ log (q.1 : ℝ) / log N = b ∨ q.1 ∣ N
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hC, e1⟩)
    by_cases e2 : log (q.2 : ℝ) / log N = lo (log (q.1 : ℝ) / log N) ∨ log (q.2 : ℝ) / log N = hi (log (q.1 : ℝ) / log N) ∨ q.2 ∣ N
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hC, e2⟩)
    exfalso
    apply hO
    push Not at e1 e2
    obtain ⟨a1, b1, d1⟩ := e1
    obtain ⟨a2, b2, d2⟩ := e2
    have ne1 : q.1 ≠ N := by rintro h; apply d1; rw [h]
    have ne2 : q.2 ≠ N := by rintro h; apply d2; rw [h]
    simp only [prcOpen, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, p1, p2, (Nat.Prime.coprime_iff_not_dvd p1).2 d1,
      (Nat.Prime.coprime_iff_not_dvd p2).2 d2,
      ⟨lt_of_le_of_ne ht.1 (Ne.symm a1), lt_of_le_of_ne ht.2 b1⟩,
      ⟨lt_of_le_of_ne hu.1 (Ne.symm a2), lt_of_le_of_ne hu.2 b2⟩⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  rw [← Finset.sum_union_inter]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)

/-- Statement identical to `prc_boundary_weighted` of `Decomp349PrimeRiemann2`, proved
from `prc_boundary_mass` and the boundedness of g on the compact region. -/
theorem prc_boundary_weighted_of_leaves {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)})
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ prcClosed a b lo hi N \ prcOpen a b lo hi N,
      |g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)|) atTop
      (𝓝 0) := by
  obtain ⟨M, hMb⟩ := (prc_region_isCompact hlo hhi hlo0 hhi1).exists_bound_of_continuousOn hg
  have hmass := prc_boundary_mass ha hab hb1 hlo hhi hlo0 hlohi hhi1 hM
  have hlim : Tendsto (fun N : ℕ => M * ∑ q ∈ prcClosed a b lo hi N \ prcOpen a b lo hi N,
      1 / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
    simpa using hmass.const_mul M
  refine squeeze_zero (fun N => Finset.sum_nonneg fun _ _ => abs_nonneg _) (fun N => ?_) hlim
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hqC := (Finset.mem_sdiff.1 hq).1
  simp only [prcClosed, Finset.mem_filter] at hqC
  obtain ⟨-, hp, hq', ht, hu⟩ := hqC
  have hpos : (0 : ℝ) < (q.1 : ℝ) * q.2 := by
    have := hp.pos; have := hq'.pos; positivity
  have hb := hMb (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) ⟨ht, hu⟩
  rw [Real.norm_eq_abs] at hb
  rw [abs_div, abs_of_pos hpos, mul_one_div]
  exact div_le_div_of_nonneg_right hb hpos.le

end LeanLab.ChenDoubleSieve.PrimeRiemannCore
