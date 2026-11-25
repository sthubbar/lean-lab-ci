import LeanLab.ChenDoubleSieve.Decomp349PrimeRiemannCore
import LeanLab.ChenDoubleSieve.Decomp349cQuadTendsto

/-!
Split of the LEAF `qt_prime_region_riemann4` of `Decomp349cQuadTendsto`, Wu 2004
arXiv 0705.1652 page 39 equation 10.5 and page 41 equation 10.12, prime partial
summation in four variables. Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41.
The closed and the open four variable region sets are defined, and the exact statement
is proved from the proved one dimensional Mertens interval limit of
`Decomp349PrimeRiemannCore` and two LEAFs: the Riemann sum over the closed region set, and the
vanishing weighted mass between the closed and the open region sets.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open PrimeRiemannCore

/-- Wu 2004 page 41 equation 10.12 with page 39 equation 10.5, the closed four variable
summation region: prime quadruples with entries at most N, t1 in the closed interval
a to b and each next coordinate in the closed interval between the curves at the
previous one. -/
def qcClosed (a b : ℝ) (l2 h2 l3 h3 l4 h4 : ℝ → ℝ) (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ
      Finset.range (N + 1)).filter fun q =>
    q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime ∧
      log (q.1 : ℝ) / log N ∈ Icc a b ∧
      log (q.2.1 : ℝ) / log N ∈ Icc (l2 (log (q.1 : ℝ) / log N)) (h2 (log (q.1 : ℝ) / log N)) ∧
      log (q.2.2.1 : ℝ) / log N ∈ Icc (l3 (log (q.2.1 : ℝ) / log N))
        (h3 (log (q.2.1 : ℝ) / log N)) ∧
      log (q.2.2.2 : ℝ) / log N ∈ Icc (l4 (log (q.2.2.1 : ℝ) / log N))
        (h4 (log (q.2.2.1 : ℝ) / log N))

/-- Wu 2004 page 41 equation 10.12 with page 39 equation 10.5, the open four variable
summation region: prime quadruples below N and coprime to N with t1 in the open interval
a to b and each next coordinate strictly between the curves at the previous one. -/
def qcOpen (a b : ℝ) (l2 h2 l3 h3 l4 h4 : ℝ → ℝ) (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N ×ˢ Finset.range N ×ˢ Finset.range N).filter fun q =>
    q.1.Prime ∧ q.2.1.Prime ∧ q.2.2.1.Prime ∧ q.2.2.2.Prime ∧
      q.1.Coprime N ∧ q.2.1.Coprime N ∧ q.2.2.1.Coprime N ∧ q.2.2.2.Coprime N ∧
      log (q.1 : ℝ) / log N ∈ Ioo a b ∧
      log (q.2.1 : ℝ) / log N ∈ Ioo (l2 (log (q.1 : ℝ) / log N)) (h2 (log (q.1 : ℝ) / log N)) ∧
      log (q.2.2.1 : ℝ) / log N ∈ Ioo (l3 (log (q.2.1 : ℝ) / log N))
        (h3 (log (q.2.1 : ℝ) / log N)) ∧
      log (q.2.2.2 : ℝ) / log N ∈ Ioo (l4 (log (q.2.2.1 : ℝ) / log N))
        (h4 (log (q.2.2.1 : ℝ) / log N))

/-- LEAF: Wu 2004 page 39 equation 10.5 and page 41 equation 10.12, the four variable
Riemann sum step over the closed region: given the one dimensional Mertens limit on every
interval, the sum over prime quadruples of the closed region of g over p1 p2 p3 p4 tends
to the iterated integral of g against dt1 dt2 dt3 dt4 over t1 t2 t3 t4, by approximating
the nested region and g with finitely many boxes. Class HARD. -/
theorem qc_closed_riemann4 {a b : ℝ} {l2 h2 l3 h3 l4 h4 : ℝ → ℝ}
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
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ qcClosed a b l2 h2 l3 h3 l4 h4 N,
      g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) atTop
      (𝓝 (∫ t1 in a..b, (∫ t2 in l2 t1..h2 t1, (∫ t3 in l3 t2..h3 t2,
        (∫ t4 in l4 t3..h4 t3, g (t1, t2, t3, t4) / t4) / t3) / t2) / t1)) := by
  sorry

/-- LEAF: Wu 2004 page 39 equation 10.5 and page 41 equation 10.12, the four variable
boundary step: given the one dimensional Mertens limit, the weighted mass of the
quadruples in the closed region set but not in the open region set tends to zero. These
lie on a boundary surface of the nested region, or have a prime dividing N or equal to N;
g is bounded on the compact region. Class MEDIUM. -/
theorem qc_boundary4 {a b : ℝ} {l2 h2 l3 h3 l4 h4 : ℝ → ℝ}
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
    (hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a'))) :
    Tendsto (fun N : ℕ => ∑ q ∈ qcClosed a b l2 h2 l3 h3 l4 h4 N \ qcOpen a b l2 h2 l3 h3 l4 h4 N,
      |g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q|) atTop (𝓝 0) := by
  sorry

/-- Statement identical to `qt_prime_region_riemann4` of `Decomp349cQuadTendsto`, Wu 2004
page 39 equation 10.5 and page 41 equation 10.12, proved from the proved
`prc_mertens_interval` and the LEAFs `qc_closed_riemann4` and `qc_boundary4`. -/
theorem qt_prime_region_riemann4_of_leaves {a b : ℝ} {l2 h2 l3 h3 l4 h4 : ℝ → ℝ}
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
  have hM : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → b' ≤ 1 →
      Tendsto (fun N : ℕ => prcMertens a' b' N) atTop (𝓝 (log b' - log a')) :=
    fun _ _ h1 h2 h3 => prc_mertens_interval h1 h2 h3
  refine prc_sandwich (qcClosed a b l2 h2 l3 h3 l4 h4) (qcOpen a b l2 h2 l3 h3 l4 h4) S
    (fun N q => g (log (q.1 : ℝ) / log N, log (q.2.1 : ℝ) / log N, log (q.2.2.1 : ℝ) / log N,
        log (q.2.2.2 : ℝ) / log N) / quadProduct q) ?_ ?_
    (qc_closed_riemann4 ha hab hb1 hl2 hh2 hl3 hh3 hl4 hh4 hr2 hr3 hr4 hg hM)
    (qc_boundary4 ha hab hb1 hl2 hh2 hl3 hh3 hl4 hh4 hr2 hr3 hr4 hg hM)
  · filter_upwards [hclosed, eventually_ge_atTop 2] with N hN hN2 q hq
    obtain ⟨p1, p2, p3, p4, t1, t2, t3, t4⟩ := hN q hq
    have e2 := (hr2 _ t1).2.2
    have e3 := (hr3 _ t1 _ t2).2.2
    have e4 := (hr4 _ t1 _ t2 _ t3).2.2
    simp only [qcClosed, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨prc_lt_succ_of_le_one hN2 p1.pos (t1.2.trans hb1),
      prc_lt_succ_of_le_one hN2 p2.pos (t2.2.trans e2),
      prc_lt_succ_of_le_one hN2 p3.pos (t3.2.trans e3),
      prc_lt_succ_of_le_one hN2 p4.pos (t4.2.trans e4)⟩,
      p1, p2, p3, p4, t1, t2, t3, t4⟩
  · filter_upwards [hopen] with N hN q hq
    simp only [qcOpen, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨⟨n1, n2, n3, n4⟩, p1, p2, p3, p4, c1, c2, c3, c4, t1, t2, t3, t4⟩ := hq
    exact hN q p1 p2 p3 p4 n1 n2 n3 n4 c1 c2 c3 c4 t1 t2 t3 t4

end LeanLab.ChenDoubleSieve.Task349.SplitSum
