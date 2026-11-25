import LeanLab.ChenDoubleSieve.Decomp349PrimeRiemannCore

/-!
Two variable prime Riemann sums, Wu 2004 arXiv 0705.1652, page 39 equation 10.5 and
page 41 equations 10.9 to 10.11. Source: https://arxiv.org/pdf/0705.1652.
The closed region set and the open region set of prime pairs, and two LEAFs: the
Riemann sum limit over the closed region set, given the one dimensional Mertens
interval limit, and the vanishing of the weighted mass between the two sets.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.PrimeRiemannCore

/-- Wu 2004 page 39 equation 10.5, the closed summation region: prime pairs p, q at most N
with t equal log p / log N in the closed interval a to b and u equal log q / log N in the
closed interval lo t to hi t. -/
def prcClosed (a b : ℝ) (lo hi : ℝ → ℝ) (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter fun q =>
    q.1.Prime ∧ q.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2 : ℝ) / log N ∈ Icc (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N))

/-- Wu 2004 page 39 equation 10.5, the open summation region: prime pairs below N and
coprime to N with t in the open interval a to b and u strictly between lo t and hi t. -/
def prcOpen (a b : ℝ) (lo hi : ℝ → ℝ) (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter fun q =>
    q.1.Prime ∧ q.2.Prime ∧ q.1.Coprime N ∧ q.2.Coprime N ∧
      log (q.1 : ℝ) / log N ∈ Ioo a b ∧
      log (q.2 : ℝ) / log N ∈ Ioo (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N))

/-- LEAF: Wu 2004 page 39 equation 10.5, the Riemann sum step over the closed region:
given the one dimensional Mertens limit on every interval, the sum over prime pairs of the
closed region of g of t and u over p q tends to the double integral of g over t u, by
approximating the region and g with finitely many rectangles. Class HARD. -/
theorem prc_closed_riemann {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)})
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ prcClosed a b lo hi N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.5, the boundary step: given the one dimensional
Mertens limit, the weighted mass of the pairs in the closed region set but not in the
open region set tends to zero. These pairs lie on the curves t equal a or b, u equal lo t
or hi t, or have a prime dividing N or equal to N; g is bounded on the compact region.
Class MEDIUM. -/
theorem prc_boundary_weighted {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
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
  sorry

/-- Wu 2004 page 39 equation 10.5 for any sets S N between `prcOpen` and `prcClosed`,
proved from the proved `prc_mertens_interval` and the LEAFs `prc_closed_riemann` and
`prc_boundary_weighted`. -/
theorem prc_region_riemann_of_sandwich {a b : ℝ} {lo hi : ℝ → ℝ} {g : ℝ × ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hlo : ContinuousOn lo (Icc a b)) (hhi : ContinuousOn hi (Icc a b))
    (hlo0 : ∀ t ∈ Icc a b, 0 < lo t) (hlohi : ∀ t ∈ Icc a b, lo t ≤ hi t)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1)
    (hg : ContinuousOn g {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (lo x.1) (hi x.1)})
    (S : ℕ → Finset (ℕ × ℕ))
    (hsub : ∀ᶠ N in atTop, S N ⊆ prcClosed a b lo hi N)
    (hsup : ∀ᶠ N in atTop, prcOpen a b lo hi N ⊆ S N) :
    Tendsto (fun N : ℕ => ∑ q ∈ S N,
      g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2)) atTop
      (𝓝 (∫ t in a..b, ∫ u in lo t..hi t, g (t, u) / (t * u))) := by
  have hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a')) :=
    fun _ _ h1 h2 h3 => prc_mertens_interval h1 h2 h3
  exact prc_sandwich (prcClosed a b lo hi) (prcOpen a b lo hi) S
    (fun N q => g (log (q.1 : ℝ) / log N, log (q.2 : ℝ) / log N) / ((q.1 : ℝ) * q.2))
    hsub hsup (prc_closed_riemann ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)
    (prc_boundary_weighted ha hab hb1 hlo hhi hlo0 hlohi hhi1 hg hM)

/-- Membership in `prcClosed` from the closed region conditions, N at least 2. -/
theorem prc_mem_closed {a b : ℝ} {lo hi : ℝ → ℝ} (hb1 : b ≤ 1)
    (hhi1 : ∀ t ∈ Icc a b, hi t ≤ 1) {N : ℕ} (hN : 2 ≤ N) {q : ℕ × ℕ}
    (p1 : q.1.Prime) (p2 : q.2.Prime) (ht : log (q.1 : ℝ) / log N ∈ Icc a b)
    (hu : log (q.2 : ℝ) / log N ∈ Icc (lo (log (q.1 : ℝ) / log N)) (hi (log (q.1 : ℝ) / log N))) :
    q ∈ prcClosed a b lo hi N := by
  simp only [prcClosed, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨prc_lt_succ_of_le_one hN p1.pos (ht.2.trans hb1),
    prc_lt_succ_of_le_one hN p2.pos (hu.2.trans (hhi1 _ ht))⟩, p1, p2, ht, hu⟩

end LeanLab.ChenDoubleSieve.PrimeRiemannCore
