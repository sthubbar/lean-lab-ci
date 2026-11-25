import LeanLab.ChenDoubleSieve.Decomp349PrimeRiemann2b

/-!
Split of the LEAF `leaf_prime_region_riemann` of `Decomp349bFreeSum`, Wu 2004
arXiv 0705.1652 page 41 displays 10.9 to 10.11, the prime pair Riemann sum limits.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
The exact statement is proved here from the results of `Decomp349PrimeRiemannCore`
and `Decomp349PrimeRiemann2`: the proved one dimensional Mertens interval limit, the proved vanishing
boundary mass of `Decomp349PrimeRiemann2b`, and the one LEAF for the Riemann sum over the
closed region set.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open PrimeRiemannCore

/-- Statement identical to `leaf_prime_region_riemann` of `Decomp349bFreeSum`, Wu 2004
page 41 displays 10.9 to 10.11, proved from the proved `prc_mertens_interval` and
`prc_boundary_weighted_of_leaves` and the one LEAF `prc_closed_riemann`. -/
theorem leaf_prime_region_riemann_of_leaves {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
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
  have hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a')) :=
    fun _ _ h1 h2 h3 => prc_mertens_interval h1 h2 h3
  refine prc_sandwich (prcClosed a b lo hi) (prcOpen a b lo hi) S
    (fun N q => g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2))
    ?_ ?_ (prc_closed_riemann ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)
    (prc_boundary_weighted_of_leaves ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)
  · filter_upwards [hclosed, eventually_ge_atTop 2] with N hN h2 q hq
    obtain ⟨p1, p2, ht, hu⟩ := hN q hq
    exact prc_mem_closed hb1 hhi1 h2 p1 p2 ht hu
  · filter_upwards [hopen] with N hN q hq
    simp only [prcOpen, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨⟨h1, h2⟩, p1, p2, -, -, ht, hu⟩ := hq
    exact hN q p1 p2 h1 h2 ht hu

end LeanLab.ChenDoubleSieve.Task349
