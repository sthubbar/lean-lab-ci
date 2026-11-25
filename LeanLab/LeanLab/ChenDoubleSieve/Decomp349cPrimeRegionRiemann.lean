import LeanLab.ChenDoubleSieve.Decomp349cPairTendsto

/-!
Split of the LEAF `pt_prime_region_riemann` of `Decomp349cPairTendsto`,
Wu 2004 arXiv 0705.1652 page 39 equation 10.5, two variable prime partial summation.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
The general sets S N are compared with the canonical open region set
`ptOpenRegion`, the pairs of primes below N and coprime to N whose coordinates
t and u lie in the open region. Two LEAFs remain: the limit over the canonical
set, and the vanishing of the difference, which lives on the boundary of the
region and on primes dividing N. The target theorem is proved from them here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open Task275 Task348 Task349
open Wu04Functional (IsBuchstab)

/-- Wu 2004 page 39 equation 10.5, the summation region of the prime partial summation.
The canonical open region set: pairs of primes below N, coprime to N, with
t equal log p over log N in the open interval a to b and u equal log q over log N
strictly between lo t and hi t. -/
def ptOpenRegion (a b : ℝ) (lo hi : ℝ → ℝ) (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter fun q =>
    q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧
      log (q.1 : ℝ) / log N ∈ Ioo a b ∧
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N))

/-- LEAF: Wu 2004 page 39 equation 10.5, prime partial summation in two variables
over the canonical open region set: the sum over prime pairs of `ptOpenRegion`
of g of t and u over p q tends to the double integral of g over t u.
Class HARD. -/
theorem pt_open_region_riemann {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)}) :
    Tendsto (fun N : ℕ => ∑ q ∈ ptOpenRegion a b lo hi N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.5, the boundary mass: for sets S N between
the closed region and the open region restricted to primes coprime to N, the
reciprocal mass of the pairs of S N outside `ptOpenRegion` tends to zero. These
pairs lie on the boundary curves t equal a or b, u equal lo t or hi t, or involve
a prime dividing N or equal to N. Class MEDIUM. -/
theorem pt_region_boundary_mass {a b : ℝ} {lo hi : ℝ → ℝ}
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
  sorry

/-- The closed region between two continuous curves is compact. -/
theorem pt_region_isCompact {a b : ℝ} {lo hi : ℝ → ℝ}
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

/-- Wu 2004 page 39 equation 10.5, the boundary terms: the weighted sum over S N
minus the sum over `ptOpenRegion` tends to zero, from the LEAF
`pt_region_boundary_mass` and the boundedness of g on the compact region. -/
theorem pt_region_boundary_negligible {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
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
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2) -
      ∑ q ∈ ptOpenRegion a b lo hi N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := (pt_region_isCompact hlo hhi hlo0 hhi1).exists_bound_of_continuousOn hg
  have hmass := pt_region_boundary_mass ha hab hb1 hlo hhi hlo0 hlohi hhi1 S hclosed hopen
  have hlim : Tendsto (fun N : ℕ => M * ∑ q ∈ S N \ ptOpenRegion a b lo hi N,
      1 / ((q.1 : ℝ) * q.2)) atTop (𝓝 0) := by
    simpa using hmass.const_mul M
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hclosed, hopen] with N hcN hoN
  have hsub : ptOpenRegion a b lo hi N ⊆ S N := by
    intro q hq
    unfold ptOpenRegion at hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨⟨h1, h2⟩, hp, hq', hc1, hc2, ht, hu⟩ := hq
    exact hoN q hp hq' h1 h2 hc1 hc2 ht hu
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro q hq
  have hqS := (Finset.mem_sdiff.1 hq).1
  obtain ⟨hp, hq', ht, hu⟩ := hcN q hqS
  have hpos : (0 : ℝ) < (q.1 : ℝ) * q.2 := by
    have := hp.pos; have := hq'.pos; positivity
  have hb := hM (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) ⟨ht, hu⟩
  rw [norm_div, Real.norm_of_nonneg hpos.le, mul_one_div]
  exact div_le_div_of_nonneg_right hb hpos.le

/-- Statement identical to `pt_prime_region_riemann`, Wu 2004 page 39 equation 10.5,
proved from the LEAFs `pt_open_region_riemann` and `pt_region_boundary_mass`. -/
theorem pt_prime_region_riemann_proved {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
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
  have hA := pt_open_region_riemann ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg
  have hB := pt_region_boundary_negligible ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg S
    hclosed hopen
  have h := hA.add hB
  rw [add_zero] at h
  refine h.congr ?_
  intro N
  ring

end LeanLab.ChenDoubleSieve.Task349.SplitSum
