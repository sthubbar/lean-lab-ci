import LeanLab.ChenDoubleSieve.Decomp349cSplitSum

/-!
Reduction of `quad13_low_tendsto`, `quad13_high_tendsto`, `quad14_low_tendsto` and
`quad14_high_tendsto` in `Decomp349cSplitSum`, Wu 2004 page 41 equation 10.12,
the F13 and F14 fourfold integrals.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
With t_i equal log p_i over log N, the refined weight unfolds to 36/5 over 1 minus t1
below the one tenth cutoff and to 8 above it, log N over log p2 is 1 over t2, and the
Buchstab argument log of N over p1 p2 p3 p4, over log p2, is 1 minus t1 minus t2 minus
t3 minus t4, over t2. On the closed regions this argument is at least 3.5 by
`fourfold13_argument` and `fourfold14_argument`, so it stays in the range where the
Buchstab function is continuous, Wu Lemma 2.10 and `IsBuchstab`.
One general four variable prime Riemann sum statement, the prime partial summation of
Wu page 39 equation 10.5 in four variables, is left as a LEAF; everything else is
proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open Task275 Task348 Task349
open Wu04Functional (IsBuchstab)

/-- LEAF: Wu 2004 page 39 equation 10.5 and page 41 equation 10.12, prime partial
summation in four variables: a fourfold sum over prime quadruples with a continuous
weight of t_i equal log p_i over log N, over a nested region with t1 between a and b
and each next coordinate between continuous curves in the previous one, tends to the
iterated integral of the weight against dt1 dt2 dt3 dt4 over t1 t2 t3 t4. The sets S N
need only lie between the closed region and the open region restricted to primes
below N coprime to N; the boundary and the primes dividing N carry vanishing
reciprocal mass. Class HARD. -/
theorem qt_prime_region_riemann4 {a b : ℝ} {l2 h2 l3 h3 l4 h4 : ℝ → ℝ}
    {g : ℝ × ℝ × ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hl2 : Continuous l2) (hh2 : Continuous h2) (hl3 : Continuous l3)
    (hh3 : Continuous h3) (hl4 : Continuous l4) (hh4 : Continuous h4)
    (hr2 : ∀ t1 ∈ Icc a b, 0 < l2 t1 ∧ l2 t1 ≤ h2 t1 ∧ h2 t1 ≤ 1)
    (hr3 : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc (l2 t1) (h2 t1), 0 < l3 t2 ∧ l3 t2 ≤ h3 t2 ∧ h3 t2 ≤ 1)
    (hr4 : ∀ t1 ∈ Icc a b, ∀ t2 ∈ Icc (l2 t1) (h2 t1), ∀ t3 ∈ Icc (l3 t2) (h3 t2),
      0 < l4 t3 ∧ l4 t3 ≤ h4 t3 ∧ h4 t3 ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ × ℝ × ℝ | x.1 ∈ Icc a b ∧
      x.2.1 ∈ Icc (l2 x.1) (h2 x.1) ∧ x.2.2.1 ∈ Icc (l3 x.2.1) (h3 x.2.1) ∧
      x.2.2.2 ∈ Icc (l4 x.2.2.1) (h4 x.2.2.1)})
    (S : ℕ → Finset (ℕ × ℕ × ℕ × ℕ))
    (hclosed : ∀ᶠ N : ℕ in atTop, ∀ q ∈ S N, q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧
      q.2.2.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2.1 : ℝ) / log N ∈ Icc (l2 (log (q.1 : ℝ) / log N)) (h2 (log (q.1 : ℝ) / log N)) ∧
      log (q.2.2.1 : ℝ) / log N ∈
        Icc (l3 (log (q.2.1 : ℝ) / log N)) (h3 (log (q.2.1 : ℝ) / log N)) ∧
      log (q.2.2.2 : ℝ) / log N ∈
        Icc (l4 (log (q.2.2.1 : ℝ) / log N)) (h4 (log (q.2.2.1 : ℝ) / log N)))
    (hopen : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ × ℕ × ℕ × ℕ, q.1.Prime → q.2.1.Prime →
      q.2.2.1.Prime → q.2.2.2.Prime → q.1 < N → q.2.1 < N → q.2.2.1 < N → q.2.2.2 < N →
      q.1.Coprime N → q.2.1.Coprime N → q.2.2.1.Coprime N → q.2.2.2.Coprime N →
      log (q.1 : ℝ) / log N ∈ Ioo a b →
      log (q.2.1 : ℝ) / log N ∈ Ioo (l2 (log (q.1 : ℝ) / log N)) (h2 (log (q.1 : ℝ) / log N)) →
      log (q.2.2.1 : ℝ) / log N ∈
        Ioo (l3 (log (q.2.1 : ℝ) / log N)) (h3 (log (q.2.1 : ℝ) / log N)) →
      log (q.2.2.2 : ℝ) / log N ∈
        Ioo (l4 (log (q.2.2.1 : ℝ) / log N)) (h4 (log (q.2.2.1 : ℝ) / log N)) →
      q ∈ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N,
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) atTop
      (𝓝 (∫ t1 in a..b, (∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, g (t1, t2, t3, t4) / t4) / t3) / t2) / t1)) := by
  sorry

/-! ## Coordinate translations, N at least 2 -/

theorem qt_rpow_le_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (N : ℝ) ^ σ ≤ p ↔ σ ≤ log (p : ℝ) / log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ hL, rpow_def_of_pos hN0, ← le_log_iff_exp_le hp0, mul_comm]

theorem qt_lt_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) < (N : ℝ) ^ σ ↔ log (p : ℝ) / log N < σ := by
  rw [← not_le, qt_rpow_le_iff hN hp σ, not_le]

theorem qt_le_rpow_iff {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (σ : ℝ) :
    (p : ℝ) ≤ (N : ℝ) ^ σ ↔ log (p : ℝ) / log N ≤ σ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hL, rpow_def_of_pos hN0, ← log_le_iff_le_exp hp0, mul_comm]

theorem qt_lt_iff {N p q : ℕ} (hN : 2 ≤ N) (hp : 0 < p) (hq : 0 < q) :
    p < q ↔ log (p : ℝ) / log N < log (q : ℝ) / log N := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_lt_div_iff_of_pos_right hL, log_lt_log_iff hp0 hq0, Nat.cast_lt]

theorem qt_lt_rpow_div_iff {N r s : ℕ} (hN : 2 ≤ N) (hr : 0 < r) (hs : 0 < s) (σ : ℝ) :
    (s : ℝ) < (N : ℝ) ^ σ / r ↔ log (s : ℝ) / log N < σ - log (r : ℝ) / log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  rw [lt_div_iff₀ hr0, ← log_lt_log_iff (by positivity) (by positivity),
    log_mul hs0.ne' hr0.ne', log_rpow hN0, lt_sub_iff_add_lt, ← add_div,
    div_lt_iff₀ hL]

/-- Membership in the F13 domain `refinedQuads N 10` in the coordinates t_i. -/
theorem qt_mem10 {N : ℕ} (hN : 2 ≤ N) (q : ℕ × ℕ × ℕ × ℕ) :
    q ∈ refinedQuads N 10 ↔ (q.1 < N ∧ q.2.1 < N ∧ q.2.2.1 < N ∧ q.2.2.2 < N) ∧
      (q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime) ∧
      (q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N) ∧
      kappa1 ≤ log (q.1 : ℝ) / log N ∧
      log (q.1 : ℝ) / log N < log (q.2.1 : ℝ) / log N ∧
      log (q.2.1 : ℝ) / log N < log (q.2.2.1 : ℝ) / log N ∧
      log (q.2.2.1 : ℝ) / log N < log (q.2.2.2 : ℝ) / log N ∧
      log (q.2.2.2 : ℝ) / log N < kappa2 := by
  unfold refinedQuads Wu08Sum.P4
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, ite_true]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, p1, p2, p3, p4, c1, c2, c3, c4, a1, a2, a3, a4, a5⟩
    exact ⟨⟨h1, h2, h3, h4⟩, ⟨p1, p2, p3, p4⟩, ⟨c1, c2, c3, c4⟩,
      (qt_rpow_le_iff hN p1.pos _).1 a1, (qt_lt_iff hN p1.pos p2.pos).1 a2,
      (qt_lt_iff hN p2.pos p3.pos).1 a3, (qt_lt_iff hN p3.pos p4.pos).1 a4,
      (qt_lt_rpow_iff hN p4.pos _).1 a5⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, ⟨p1, p2, p3, p4⟩, ⟨c1, c2, c3, c4⟩, a1, a2, a3, a4, a5⟩
    exact ⟨⟨h1, h2, h3, h4⟩, p1, p2, p3, p4, c1, c2, c3, c4,
      (qt_rpow_le_iff hN p1.pos _).2 a1, (qt_lt_iff hN p1.pos p2.pos).2 a2,
      (qt_lt_iff hN p2.pos p3.pos).2 a3, (qt_lt_iff hN p3.pos p4.pos).2 a4,
      (qt_lt_rpow_iff hN p4.pos _).2 a5⟩

/-- Membership in the F14 domain `refinedQuads N 11` in the coordinates t_i. -/
theorem qt_mem11 {N : ℕ} (hN : 2 ≤ N) (q : ℕ × ℕ × ℕ × ℕ) :
    q ∈ refinedQuads N 11 ↔ (q.1 < N ∧ q.2.1 < N ∧ q.2.2.1 < N ∧ q.2.2.2 < N) ∧
      (q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime) ∧
      (q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N) ∧
      kappa1 ≤ log (q.1 : ℝ) / log N ∧
      log (q.1 : ℝ) / log N < log (q.2.1 : ℝ) / log N ∧
      log (q.2.1 : ℝ) / log N < log (q.2.2.1 : ℝ) / log N ∧
      log (q.2.2.1 : ℝ) / log N < kappa2 ∧
      kappa2 ≤ log (q.2.2.2 : ℝ) / log N ∧
      log (q.2.2.2 : ℝ) / log N < 1 / 2 - 2 * kappa1 - log (q.2.2.1 : ℝ) / log N := by
  unfold refinedQuads Wu08Sum.P4
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    show (11 : Fin 12) ≠ 10 by decide, if_false]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, p1, p2, p3, p4, c1, c2, c3, c4, a1, a2, a3, a4, a5, a6⟩
    exact ⟨⟨h1, h2, h3, h4⟩, ⟨p1, p2, p3, p4⟩, ⟨c1, c2, c3, c4⟩,
      (qt_rpow_le_iff hN p1.pos _).1 a1, (qt_lt_iff hN p1.pos p2.pos).1 a2,
      (qt_lt_iff hN p2.pos p3.pos).1 a3, (qt_lt_rpow_iff hN p3.pos _).1 a4,
      (qt_rpow_le_iff hN p4.pos _).1 a5, (qt_lt_rpow_div_iff hN p3.pos p4.pos _).1 a6⟩
  · rintro ⟨⟨h1, h2, h3, h4⟩, ⟨p1, p2, p3, p4⟩, ⟨c1, c2, c3, c4⟩, a1, a2, a3, a4, a5, a6⟩
    exact ⟨⟨h1, h2, h3, h4⟩, p1, p2, p3, p4, c1, c2, c3, c4,
      (qt_rpow_le_iff hN p1.pos _).2 a1, (qt_lt_iff hN p1.pos p2.pos).2 a2,
      (qt_lt_iff hN p2.pos p3.pos).2 a3, (qt_lt_rpow_iff hN p3.pos _).2 a4,
      (qt_rpow_le_iff hN p4.pos _).2 a5, (qt_lt_rpow_div_iff hN p3.pos p4.pos _).2 a6⟩

/-- The summand identity: with t_i equal log p_i over log N, log N times
w times omega of log of N over the product, over log p2, divided by the product
times log p2, equals w over t2 times omega of 1 minus the t_i over t2, divided by
the product. -/
theorem qt_summand {N : ℕ} (hN : 2 ≤ N) (q : ℕ × ℕ × ℕ × ℕ) (h1 : 0 < q.1)
    (h2 : 1 < q.2.1) (h3 : 0 < q.2.2.1) (h4 : 0 < q.2.2.2) (w : ℝ) (ω : ℝ → ℝ) :
    log N * (w * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
      (quadProduct q * log q.2.1)) =
    w / (log (q.2.1 : ℝ) / log N) *
      ω ((1 - log (q.1 : ℝ) / log N - log (q.2.1 : ℝ) / log N -
        log (q.2.2.1 : ℝ) / log N - log (q.2.2.2 : ℝ) / log N) /
        (log (q.2.1 : ℝ) / log N)) / quadProduct q := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have p1 : (0 : ℝ) < q.1 := by exact_mod_cast h1
  have p2 : (0 : ℝ) < q.2.1 := by exact_mod_cast (by omega : 0 < q.2.1)
  have p3 : (0 : ℝ) < q.2.2.1 := by exact_mod_cast h3
  have p4 : (0 : ℝ) < q.2.2.2 := by exact_mod_cast h4
  have hl2 : 0 < log (q.2.1 : ℝ) := log_pos (by exact_mod_cast h2)
  have harg : log ((N : ℝ) / quadProduct q) / log q.2.1 =
      (1 - log (q.1 : ℝ) / log N - log (q.2.1 : ℝ) / log N -
        log (q.2.2.1 : ℝ) / log N - log (q.2.2.2 : ℝ) / log N) /
        (log (q.2.1 : ℝ) / log N) := by
    unfold quadProduct
    rw [log_div hN0.ne' (by positivity), log_mul (by positivity) p4.ne',
      log_mul (by positivity) p3.ne', log_mul p1.ne' p2.ne']
    field_simp
    ring
  rw [harg]
  field_simp

/-! ## Algebra of the iterated integrals -/

/-- The LEAF's iterated integral with the weight c of t1 over t2 times the Buchstab
factor is c times t1 over the weight, times Wu's `fourfold` integrand form. -/
theorem qt_integral_eq (ω : ℝ → ℝ) (c : ℝ → ℝ) (a b : ℝ) (l2 h2 l3 h3 l4 h4 : ℝ → ℝ) :
    (∫ t1 in a..b, (∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, c t1 / t2 * ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) /
          t2) / t1) =
    ∫ t1 in a..b, c t1 * ((∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) /
          t2 ^ 2) / t1) := by
  refine intervalIntegral.integral_congr (fun t1 _ => ?_)
  try simp only
  have e2 : (∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, c t1 / t2 * ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) /
          t2) = c t1 * ∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) / t2 ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t2 _ => ?_)
    try simp only
    have e3 : (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, c t1 / t2 * ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) =
        c t1 / t2 * ∫ t3 in l3 t2..h3 t2,
          (∫ t4 in l4 t3..h4 t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t3 _ => ?_)
      try simp only
      have e4 : (∫ t4 in l4 t3..h4 t3, c t1 / t2 * ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) =
          c t1 / t2 * ∫ t4 in l4 t3..h4 t3, ω ((1 - t1 - t2 - t3 - t4) / t2) / t4 := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr (fun t4 _ => ?_)
        try simp only
        ring
      rw [e4]
      ring
    rw [e3]
    ring
  rw [e2]
  ring

/-! ## Continuity of the weights, Wu Lemma 2.10 range -/

theorem qt_cont13 (ω : ℝ → ℝ) (hω : IsBuchstab ω) (c : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn c (Icc a b))
    (ha : 0 < a) (hb : b ≤ kappa2) :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ => c x.1 / x.2.1 *
        ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1))
      {x : ℝ × ℝ × ℝ × ℝ | x.1 ∈ Icc a b ∧
      x.2.1 ∈ Icc (id x.1) ((fun _ => kappa2) x.1) ∧
      x.2.2.1 ∈ Icc (id x.2.1) ((fun _ => kappa2) x.2.1) ∧
      x.2.2.2 ∈ Icc (id x.2.2.1) ((fun _ => kappa2) x.2.2.1)} := by
  have hpos : ∀ x ∈ {x : ℝ × ℝ × ℝ × ℝ | x.1 ∈ Icc a b ∧
      x.2.1 ∈ Icc (id x.1) ((fun _ => kappa2) x.1) ∧
      x.2.2.1 ∈ Icc (id x.2.1) ((fun _ => kappa2) x.2.1) ∧
      x.2.2.2 ∈ Icc (id x.2.2.1) ((fun _ => kappa2) x.2.2.1)}, 0 < x.2.1 := by
    intro x hx
    obtain ⟨⟨a1, _⟩, ⟨a2, _⟩, _⟩ := hx
    simp only [id] at a2
    linarith
  apply ContinuousOn.mul
  · exact ContinuousOn.div (hc.comp (by fun_prop) (fun x hx => hx.1)) (by fun_prop)
      (fun x hx => (hpos x hx).ne')
  · refine hω.1.comp (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => (hpos x hx).ne')) ?_
    intro x hx
    have h0 := hpos x hx
    obtain ⟨⟨_, b1⟩, ⟨_, b2⟩, ⟨_, b3⟩, ⟨_, b4⟩⟩ := hx
    have := fourfold13_argument x.1 x.2.1 x.2.2.1 x.2.2.2 h0 (by linarith) b2 b3 b4
    rw [Set.mem_Ici]
    linarith

theorem qt_cont14 (ω : ℝ → ℝ) (hω : IsBuchstab ω) (c : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn c (Icc a b))
    (ha : 0 < a) (hb : b ≤ kappa2) :
    ContinuousOn (fun x : ℝ × ℝ × ℝ × ℝ => c x.1 / x.2.1 *
        ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1))
      {x : ℝ × ℝ × ℝ × ℝ | x.1 ∈ Icc a b ∧
      x.2.1 ∈ Icc (id x.1) ((fun _ => kappa2) x.1) ∧
      x.2.2.1 ∈ Icc (id x.2.1) ((fun _ => kappa2) x.2.1) ∧
      x.2.2.2 ∈ Icc ((fun _ => kappa2) x.2.2.1) ((fun t => 1 / 2 - 2 * kappa1 - t) x.2.2.1)} := by
  have hpos : ∀ x ∈ {x : ℝ × ℝ × ℝ × ℝ | x.1 ∈ Icc a b ∧
      x.2.1 ∈ Icc (id x.1) ((fun _ => kappa2) x.1) ∧
      x.2.2.1 ∈ Icc (id x.2.1) ((fun _ => kappa2) x.2.1) ∧
      x.2.2.2 ∈ Icc ((fun _ => kappa2) x.2.2.1) ((fun t => 1 / 2 - 2 * kappa1 - t) x.2.2.1)},
      0 < x.2.1 := by
    intro x hx
    obtain ⟨⟨a1, _⟩, ⟨a2, _⟩, _⟩ := hx
    simp only [id] at a2
    linarith
  apply ContinuousOn.mul
  · exact ContinuousOn.div (hc.comp (by fun_prop) (fun x hx => hx.1)) (by fun_prop)
      (fun x hx => (hpos x hx).ne')
  · refine hω.1.comp (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun x hx => (hpos x hx).ne')) ?_
    intro x hx
    have h0 := hpos x hx
    obtain ⟨⟨_, b1⟩, ⟨_, b2⟩, _, ⟨_, b4⟩⟩ := hx
    have := fourfold14_argument x.1 x.2.1 x.2.2.1 x.2.2.2 h0 (by linarith) b2 b4
    rw [Set.mem_Ici]
    linarith


/-- Statement identical to `quad13_low_tendsto`, Wu 2004 page 41 equation 10.12, proved from the
LEAF `qt_prime_region_riemann4`. -/
theorem quad13_low_tendsto_proved (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (36 / 5 * fourfold ω (fun _ => kappa2) kappa1 (1 / 10) id
        (fun t => t * (1 - t)))) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk10 : kappa1 < (1 / 10 : ℝ) := by norm_num [kappa1]
  have h10k : (1 / 10 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk21 : kappa2 < 1 / 2 - 2 * kappa1 - kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : kappa2 ≤ 1 := by norm_num [kappa2]
  have hk3 : 2 * kappa1 ≤ 1 / 2 := by norm_num [kappa1]
  let c : ℝ → ℝ := fun t => 36 / 5 / (1 - t)
  have hc : ContinuousOn c (Icc kappa1 (1 / 10)) := by
    exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun t ht => (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne')
  let g : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => c x.1 / x.2.1 *
    ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1)
  have hg := qt_cont13 ω hω c kappa1 (1 / 10) hc (by linarith) (by linarith)
  have hR := qt_prime_region_riemann4 (a := kappa1) (b := (1 / 10)) (l2 := id)
    (h2 := fun _ => kappa2) (l3 := id) (h3 := fun _ => kappa2) (l4 := id)
    (h4 := fun _ => kappa2) (g := g) (by linarith) (by linarith) (by linarith)
    continuous_id continuous_const continuous_id continuous_const (by fun_prop) (by fun_prop)
    (fun t ht => ⟨by simp only [id]; linarith [ht.1], by simp only [id]; linarith [ht.2], hk2⟩)
    (fun t ht u hu => ⟨by simp only [id] at hu ⊢; linarith [ht.1, hu.1],
      by simp only [id]; linarith [hu.2], hk2⟩)
    (fun t ht u hu v hv => by
      simp only [id] at ht hu hv ⊢
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨hv1, hv2⟩ := hv
      refine ⟨?_, ?_, ?_⟩ <;> linarith)
    hg
    (fun N => (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, qt_mem10 hN] at hq
      obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _, a1, a2, a3, a4, a5⟩, h10⟩ := hq
      exact ⟨p1, p2, p3, p4, ⟨a1, (qt_le_rpow_iff hN p1.pos _).1 h10⟩, ⟨a2.le, by linarith⟩, ⟨a3.le, by linarith⟩, ⟨a4.le, a5.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp1 hp2 hp3 hp4 h1 h2 h3 h4 c1 c2 c3 c4
        ht1 ht2 ht3 ht4
      simp only [id] at ht2 ht3 ht4
      rw [Finset.mem_filter, qt_mem10 hN]
      exact ⟨⟨⟨h1, h2, h3, h4⟩, ⟨hp1, hp2, hp3, hp4⟩, ⟨c1, c2, c3, c4⟩, ht1.1.le, ht2.1,
        ht3.1, ht4.1, ht4.2⟩, (qt_le_rpow_iff hN hp1.pos _).2 ht1.2.le⟩)
  have hlim := qt_integral_eq ω c kappa1 (1 / 10) id (fun _ => kappa2) id (fun _ => kappa2)
    (id) (fun _ => kappa2)
  refine Tendsto.congr' (f₁ := fun N => ∑ q ∈ (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 := hq
    rw [Finset.mem_filter, qt_mem10 hN] at hq2
    obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _⟩, h10⟩ := hq2
    unfold refinedWeight
    rw [if_pos h10, qt_summand hN q p1.pos p2.one_lt p3.pos p4.pos]
  · convert hR using 2
    refine (hlim.trans ?_).symm
    unfold fourfold
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t1 _ => ?_)
    simp only [id, c, div_eq_mul_inv, mul_inv] <;> ring

/-- Statement identical to `quad13_high_tendsto`, Wu 2004 page 41 equation 10.12, proved from the
LEAF `qt_prime_region_riemann4`. -/
theorem quad13_high_tendsto_proved (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (8 * fourfold ω (fun _ => kappa2) (1 / 10) kappa2 id
        id)) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk10 : kappa1 < (1 / 10 : ℝ) := by norm_num [kappa1]
  have h10k : (1 / 10 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk21 : kappa2 < 1 / 2 - 2 * kappa1 - kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : kappa2 ≤ 1 := by norm_num [kappa2]
  have hk3 : 2 * kappa1 ≤ 1 / 2 := by norm_num [kappa1]
  let c : ℝ → ℝ := fun _ => 8
  have hc : ContinuousOn c (Icc (1 / 10) kappa2) := by exact continuousOn_const
  let g : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => c x.1 / x.2.1 *
    ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1)
  have hg := qt_cont13 ω hω c (1 / 10) kappa2 hc (by linarith) (by linarith)
  have hR := qt_prime_region_riemann4 (a := (1 / 10)) (b := kappa2) (l2 := id)
    (h2 := fun _ => kappa2) (l3 := id) (h3 := fun _ => kappa2) (l4 := id)
    (h4 := fun _ => kappa2) (g := g) (by linarith) (by linarith) (by linarith)
    continuous_id continuous_const continuous_id continuous_const (by fun_prop) (by fun_prop)
    (fun t ht => ⟨by simp only [id]; linarith [ht.1], by simp only [id]; linarith [ht.2], hk2⟩)
    (fun t ht u hu => ⟨by simp only [id] at hu ⊢; linarith [ht.1, hu.1],
      by simp only [id]; linarith [hu.2], hk2⟩)
    (fun t ht u hu v hv => by
      simp only [id] at ht hu hv ⊢
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨hv1, hv2⟩ := hv
      refine ⟨?_, ?_, ?_⟩ <;> linarith)
    hg
    (fun N => (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, qt_mem10 hN] at hq
      obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _, a1, a2, a3, a4, a5⟩, h10⟩ := hq
      rw [qt_le_rpow_iff hN p1.pos, not_le] at h10
      exact ⟨p1, p2, p3, p4, ⟨h10.le, by linarith⟩, ⟨a2.le, by linarith⟩, ⟨a3.le, by linarith⟩, ⟨a4.le, a5.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp1 hp2 hp3 hp4 h1 h2 h3 h4 c1 c2 c3 c4
        ht1 ht2 ht3 ht4
      simp only [id] at ht2 ht3 ht4
      rw [Finset.mem_filter, qt_mem10 hN]
      exact ⟨⟨⟨h1, h2, h3, h4⟩, ⟨hp1, hp2, hp3, hp4⟩, ⟨c1, c2, c3, c4⟩, (by linarith [ht1.1]), ht2.1,
        ht3.1, ht4.1, ht4.2⟩, by rw [qt_le_rpow_iff hN hp1.pos, not_le]; exact ht1.1⟩)
  have hlim := qt_integral_eq ω c (1 / 10) kappa2 id (fun _ => kappa2) id (fun _ => kappa2)
    (id) (fun _ => kappa2)
  refine Tendsto.congr' (f₁ := fun N => ∑ q ∈ (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 := hq
    rw [Finset.mem_filter, qt_mem10 hN] at hq2
    obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _⟩, h10⟩ := hq2
    unfold refinedWeight
    rw [if_neg h10, qt_summand hN q p1.pos p2.one_lt p3.pos p4.pos]
  · convert hR using 2
    refine (hlim.trans ?_).symm
    unfold fourfold
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t1 _ => ?_)
    simp only [id, c, div_eq_mul_inv, mul_inv] <;> ring

/-- Statement identical to `quad14_low_tendsto`, Wu 2004 page 41 equation 10.12, proved from the
LEAF `qt_prime_region_riemann4`. -/
theorem quad14_low_tendsto_proved (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (36 / 5 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10) (fun _ => kappa2)
        (fun t => t * (1 - t)))) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk10 : kappa1 < (1 / 10 : ℝ) := by norm_num [kappa1]
  have h10k : (1 / 10 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk21 : kappa2 < 1 / 2 - 2 * kappa1 - kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : kappa2 ≤ 1 := by norm_num [kappa2]
  have hk3 : 2 * kappa1 ≤ 1 / 2 := by norm_num [kappa1]
  let c : ℝ → ℝ := fun t => 36 / 5 / (1 - t)
  have hc : ContinuousOn c (Icc kappa1 (1 / 10)) := by
    exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun t ht => (by linarith [ht.2] : (0 : ℝ) < 1 - t).ne')
  let g : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => c x.1 / x.2.1 *
    ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1)
  have hg := qt_cont14 ω hω c kappa1 (1 / 10) hc (by linarith) (by linarith)
  have hR := qt_prime_region_riemann4 (a := kappa1) (b := (1 / 10)) (l2 := id)
    (h2 := fun _ => kappa2) (l3 := id) (h3 := fun _ => kappa2) (l4 := fun _ => kappa2)
    (h4 := fun t => 1 / 2 - 2 * kappa1 - t) (g := g) (by linarith) (by linarith) (by linarith)
    continuous_id continuous_const continuous_id continuous_const (by fun_prop) (by fun_prop)
    (fun t ht => ⟨by simp only [id]; linarith [ht.1], by simp only [id]; linarith [ht.2], hk2⟩)
    (fun t ht u hu => ⟨by simp only [id] at hu ⊢; linarith [ht.1, hu.1],
      by simp only [id]; linarith [hu.2], hk2⟩)
    (fun t ht u hu v hv => by
      simp only [id] at ht hu hv ⊢
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨hv1, hv2⟩ := hv
      refine ⟨?_, ?_, ?_⟩ <;> linarith)
    hg
    (fun N => (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, qt_mem11 hN] at hq
      obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _, a1, a2, a3, a4, a5, a6⟩, h10⟩ := hq
      exact ⟨p1, p2, p3, p4, ⟨a1, (qt_le_rpow_iff hN p1.pos _).1 h10⟩, ⟨a2.le, by linarith⟩, ⟨a3.le, a4.le⟩, ⟨a5, a6.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp1 hp2 hp3 hp4 h1 h2 h3 h4 c1 c2 c3 c4
        ht1 ht2 ht3 ht4
      simp only [id] at ht2 ht3 ht4
      rw [Finset.mem_filter, qt_mem11 hN]
      exact ⟨⟨⟨h1, h2, h3, h4⟩, ⟨hp1, hp2, hp3, hp4⟩, ⟨c1, c2, c3, c4⟩, ht1.1.le, ht2.1,
        ht3.1, ht3.2, ht4.1.le, ht4.2⟩, (qt_le_rpow_iff hN hp1.pos _).2 ht1.2.le⟩)
  have hlim := qt_integral_eq ω c kappa1 (1 / 10) id (fun _ => kappa2) id (fun _ => kappa2)
    (fun _ => kappa2) (fun t => 1 / 2 - 2 * kappa1 - t)
  refine Tendsto.congr' (f₁ := fun N => ∑ q ∈ (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 := hq
    rw [Finset.mem_filter, qt_mem11 hN] at hq2
    obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _⟩, h10⟩ := hq2
    unfold refinedWeight
    rw [if_pos h10, qt_summand hN q p1.pos p2.one_lt p3.pos p4.pos]
  · convert hR using 2
    refine (hlim.trans ?_).symm
    unfold fourfold
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t1 _ => ?_)
    simp only [id, c, div_eq_mul_inv, mul_inv] <;> ring

/-- Statement identical to `quad14_high_tendsto`, Wu 2004 page 41 equation 10.12, proved from the
LEAF `qt_prime_region_riemann4`. -/
theorem quad14_high_tendsto_proved (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (8 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2 (fun _ => kappa2)
        id)) := by
  have hk : (0 : ℝ) < kappa1 := by norm_num [kappa1]
  have hk10 : kappa1 < (1 / 10 : ℝ) := by norm_num [kappa1]
  have h10k : (1 / 10 : ℝ) < kappa2 := by norm_num [kappa2]
  have hk21 : kappa2 < 1 / 2 - 2 * kappa1 - kappa2 := by norm_num [kappa1, kappa2]
  have hk2 : kappa2 ≤ 1 := by norm_num [kappa2]
  have hk3 : 2 * kappa1 ≤ 1 / 2 := by norm_num [kappa1]
  let c : ℝ → ℝ := fun _ => 8
  have hc : ContinuousOn c (Icc (1 / 10) kappa2) := by exact continuousOn_const
  let g : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => c x.1 / x.2.1 *
    ω ((1 - x.1 - x.2.1 - x.2.2.1 - x.2.2.2) / x.2.1)
  have hg := qt_cont14 ω hω c (1 / 10) kappa2 hc (by linarith) (by linarith)
  have hR := qt_prime_region_riemann4 (a := (1 / 10)) (b := kappa2) (l2 := id)
    (h2 := fun _ => kappa2) (l3 := id) (h3 := fun _ => kappa2) (l4 := fun _ => kappa2)
    (h4 := fun t => 1 / 2 - 2 * kappa1 - t) (g := g) (by linarith) (by linarith) (by linarith)
    continuous_id continuous_const continuous_id continuous_const (by fun_prop) (by fun_prop)
    (fun t ht => ⟨by simp only [id]; linarith [ht.1], by simp only [id]; linarith [ht.2], hk2⟩)
    (fun t ht u hu => ⟨by simp only [id] at hu ⊢; linarith [ht.1, hu.1],
      by simp only [id]; linarith [hu.2], hk2⟩)
    (fun t ht u hu v hv => by
      simp only [id] at ht hu hv ⊢
      obtain ⟨ht1, ht2⟩ := ht
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨hv1, hv2⟩ := hv
      refine ⟨?_, ?_, ?_⟩ <;> linarith)
    hg
    (fun N => (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hq
      rw [Finset.mem_filter, qt_mem11 hN] at hq
      obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _, a1, a2, a3, a4, a5, a6⟩, h10⟩ := hq
      rw [qt_le_rpow_iff hN p1.pos, not_le] at h10
      exact ⟨p1, p2, p3, p4, ⟨h10.le, by linarith⟩, ⟨a2.le, by linarith⟩, ⟨a3.le, a4.le⟩, ⟨a5, a6.le⟩⟩)
    (by
      filter_upwards [eventually_ge_atTop 2] with N hN q hp1 hp2 hp3 hp4 h1 h2 h3 h4 c1 c2 c3 c4
        ht1 ht2 ht3 ht4
      simp only [id] at ht2 ht3 ht4
      rw [Finset.mem_filter, qt_mem11 hN]
      exact ⟨⟨⟨h1, h2, h3, h4⟩, ⟨hp1, hp2, hp3, hp4⟩, ⟨c1, c2, c3, c4⟩, (by linarith [ht1.1]), ht2.1,
        ht3.1, ht3.2, ht4.1.le, ht4.2⟩, by rw [qt_le_rpow_iff hN hp1.pos, not_le]; exact ht1.1⟩)
  have hlim := qt_integral_eq ω c (1 / 10) kappa2 id (fun _ => kappa2) id (fun _ => kappa2)
    (fun _ => kappa2) (fun t => 1 / 2 - 2 * kappa1 - t)
  refine Tendsto.congr' (f₁ := fun N => ∑ q ∈ (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 := hq
    rw [Finset.mem_filter, qt_mem11 hN] at hq2
    obtain ⟨⟨_, ⟨p1, p2, p3, p4⟩, _⟩, h10⟩ := hq2
    unfold refinedWeight
    rw [if_neg h10, qt_summand hN q p1.pos p2.one_lt p3.pos p4.pos]
  · convert hR using 2
    refine (hlim.trans ?_).symm
    unfold fourfold
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t1 _ => ?_)
    simp only [id, c, div_eq_mul_inv, mul_inv] <;> ring

end LeanLab.ChenDoubleSieve.Task349.SplitSum
