import LeanLab.ChenDoubleSieve.Decomp349PrimeRiemann2b
import LeanLab.ChenDoubleSieve.Decomp349cPrimeRegionRiemann

/-!
Split of the LEAFs `pt_open_region_riemann` and `pt_region_boundary_mass` of
`Decomp349cPrimeRegionRiemann`, Wu 2004 arXiv 0705.1652 page 39 equation 10.5 and
page 41 displays 10.9 to 10.11. Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
Both exact statements are proved here from the results of `Decomp349PrimeRiemannCore`
and `Decomp349PrimeRiemann2`: the proved one dimensional Mertens interval limit, the proved vanishing
boundary mass of `Decomp349PrimeRiemann2b`, and the one LEAF for the Riemann sum over the
closed region set.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open PrimeRiemannCore

/-- `ptOpenRegion` is the set `prcOpen`. -/
theorem pt_open_eq_prcOpen (a b : ℝ) (lo hi : ℝ → ℝ) (N : ℕ) :
    ptOpenRegion a b lo hi N = prcOpen a b lo hi N := by
  ext q
  simp only [ptOpenRegion, prcOpen]

/-- `ptOpenRegion` lies in `prcClosed`. -/
theorem pt_open_sub_prcClosed (a b : ℝ) (lo hi : ℝ → ℝ) (N : ℕ) :
    ptOpenRegion a b lo hi N ⊆ prcClosed a b lo hi N := by
  intro q hq
  simp only [ptOpenRegion, prcClosed, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range] at hq ⊢
  obtain ⟨⟨h1, h2⟩, p1, p2, -, -, ht, hu⟩ := hq
  exact ⟨⟨by omega, by omega⟩, p1, p2, Ioo_subset_Icc_self ht, Ioo_subset_Icc_self hu⟩

/-- Statement identical to `pt_open_region_riemann` of `Decomp349cPrimeRegionRiemann`,
Wu 2004 page 39 equation 10.5, proved from the proved `prc_mertens_interval` and
`prc_boundary_weighted_of_leaves` and the one LEAF `prc_closed_riemann`. -/
theorem pt_open_region_riemann_of_leaves {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)}) :
    Tendsto (fun N : ℕ => ∑ q ∈ ptOpenRegion a b lo hi N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  have hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a')) :=
    fun _ _ h1 h2 h3 => prc_mertens_interval h1 h2 h3
  exact prc_sandwich (prcClosed a b lo hi) (prcOpen a b lo hi) (ptOpenRegion a b lo hi)
    (fun N q => g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2))
    (Eventually.of_forall (pt_open_sub_prcClosed a b lo hi))
    (Eventually.of_forall (fun N => (pt_open_eq_prcOpen a b lo hi N).symm.subset))
    (prc_closed_riemann ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)
    (prc_boundary_weighted_of_leaves ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)

/-- Statement identical to `pt_region_boundary_mass` of `Decomp349cPrimeRegionRiemann`,
Wu 2004 page 39 equation 10.5, proved from the proved `prc_mertens_interval` and
`prc_boundary_weighted_of_leaves` with the constant weight 1. -/
theorem pt_region_boundary_mass_of_leaves {a b : ℝ} {lo hi : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (S : ℕ → Finset (ℕ × ℕ))
    (hclosed : ∀ᶠ N : ℕ in atTop, ∀ q ∈ S N, q.1.Prime ∧ q.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2 : ℝ) / log N ∈ Icc (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)))
    (hopen : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ × ℕ, q.1.Prime → q.2.Prime → q.1 < N → q.2 < N →
      q.1.Coprime N → q.2.Coprime N →
      log (q.1 : ℝ) / log N ∈ Ioo a b →
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N)) →
      q ∈ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N \ ptOpenRegion a b lo hi N, 1 / ((q.1 : ℝ) * q.2))
      atTop (𝓝 0) := by
  have hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a')) :=
    fun _ _ h1 h2 h3 => prc_mertens_interval h1 h2 h3
  have hB := prc_boundary_weighted_of_leaves (g := fun _ => (1 : ℝ)) ha hab hb1 hlo hhi hlo0 hlohi
    hhi1 continuousOn_const hM
  refine squeeze_zero' ?_ ?_ hB
  · exact Eventually.of_forall fun N => Finset.sum_nonneg fun q _ => by positivity
  · filter_upwards [hclosed, eventually_ge_atTop 2] with N hN h2
    have hsub : S N \ ptOpenRegion a b lo hi N ⊆ prcClosed a b lo hi N \ prcOpen a b lo hi N := by
      rw [pt_open_eq_prcOpen]
      refine Finset.sdiff_subset_sdiff ?_ le_rfl
      intro q hq
      obtain ⟨p1, p2, ht, hu⟩ := hN q hq
      exact prc_mem_closed hb1 hhi1 h2 p1 p2 ht hu
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _).trans' ?_
    exact Finset.sum_le_sum fun q _ => le_abs_self _

end LeanLab.ChenDoubleSieve.Task349.SplitSum
