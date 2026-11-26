import LeanLab.ChenDoubleSieve.Decomp349c

/-!
Split of `refined_sum_tendsto` from Decomp349c.
Wu 2004 page 41 equation 10.12: prime partial summation turns each finite
refined sum into the printed integrals. The one tenth cutoff on the first prime
separates the `36/5` piece from the weight eight piece, one LEAF each.
Source: https://arxiv.org/pdf/0705.1652, page 41.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349.SplitSum
open Task275 Task348 Task349
open Wu04Functional (IsBuchstab)

/-- LEAF: Wu 2004 page 41 equation 10.12, F9 first integral: prime partial
summation over `N^kappa1 ≤ p1 ≤ N^(1/10)`, `N^sigma1 ≤ p2 < (N/p1)^(1/2)`;
the inner `p2` sum gives `log(1/σ1 - 1 - t/σ1) / (1 - t)`. Class HARD. -/
theorem pair_low_tendsto :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedPairs N).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2))))
      atTop (𝓝 (36 / 5 * ∫ t in kappa1..(1 / 10 : ℝ),
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2))) := by
  -- Obstruction: converting this two-dimensional prime sum over the curved domain
  -- {N^kappa1 ≤ p ≤ N^(1/10), N^sigma1 ≤ q < sqrt(N/p)} with weight
  -- 1/(p q (1 - log p/log N - log q/log N)) into the printed double integral requires
  -- a prime partial summation lemma with uniform error control over that domain.
  -- Mathlib v4.35.0 has Nat.primeCounting (π) but NO Prime Number Theorem
  -- (π(x) ~ x/log x), NO prime partial summation, NO sum-over-primes tendsto lemmas.
  -- The repo's PNTPort/StrongPNT exists but its PNT lemma was not integrated here.
  -- The sibling file Decomp349bSplitSum leaves the analogous leaf_free_sum_tendsto
  -- as a Class HARD sorry with no prime-sum-to-integral machinery.
  -- This sorry requires PNT + 2D prime partial summation, OUT OF REACH in v4.35.0.
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, F9 second integral, first prime
above `N^(1/10)` with weight eight. Class HARD. -/
theorem pair_high_tendsto :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedPairs N).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2))))
      atTop (𝓝 (8 * ∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)))) := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, F13 first fourfold integral over
`kappa1 ≤ t1 ≤ 1/10`, prime partial summation in four variables with the
Buchstab factor, continuous on the range of Lemma 2.10. Class HARD. -/
theorem quad13_low_tendsto (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 10).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (36 / 5 * fourfold ω (fun _ => kappa2) kappa1 (1 / 10) id
        (fun t => t * (1 - t)))) := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, F13 second fourfold integral over
`1/10 < t1 < kappa2` with weight eight. Class HARD. -/
theorem quad13_high_tendsto (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 10).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (8 * fourfold ω (fun _ => kappa2) (1 / 10) kappa2 id id)) := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, F14 first fourfold integral over
`kappa1 ≤ t1 ≤ 1/10`, with `kappa2 ≤ t4 < 1/2 - 2 kappa1 - t3`. Class HARD. -/
theorem quad14_low_tendsto (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 11).filter (fun q => (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (36 / 5 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10)
        (fun _ => kappa2) (fun t => t * (1 - t)))) := by
  sorry

/-- LEAF: Wu 2004 page 41 equation 10.12, F14 second fourfold integral over
`1/10 < t1 < kappa2` with weight eight. Class HARD. -/
theorem quad14_high_tendsto (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    Tendsto (fun N : ℕ => log N *
      ∑ q ∈ (refinedQuads N 11).filter (fun q => ¬ (q.1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)),
        refinedWeight N q.1 * ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
          (quadProduct q * log q.2.1))
      atTop (𝓝 (8 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2
        (fun _ => kappa2) id)) := by
  sorry

/-- Glue: two limits of the split pieces give the limit of the whole sum
along the even filter. -/
theorem split_tendsto {α : Type*} (s : ℕ → Finset α) (p : ℕ → α → Prop)
    [∀ N, DecidablePred (p N)] (g : ℕ → α → ℝ) (A B : ℝ)
    (hlo : Tendsto (fun N : ℕ => log N * ∑ x ∈ (s N).filter (p N), g N x) atTop (𝓝 A))
    (hhi : Tendsto (fun N : ℕ => log N * ∑ x ∈ (s N).filter (fun x => ¬ p N x), g N x)
      atTop (𝓝 B)) :
    Tendsto (fun N : ℕ => log N * ∑ x ∈ s N, g N x) evenAtTop (𝓝 (A + B)) := by
  have h : evenAtTop ≤ atTop := inf_le_left
  refine ((hlo.add hhi).mono_left h).congr' (Eventually.of_forall fun N => ?_)
  simp only
  rw [← mul_add, sum_filter_add_sum_filter_not]

/-- The exact statement of `refined_sum_tendsto`, assembled from the six LEAFs.
CONDITIONAL ON the LEAFs above. -/
theorem refined_sum_tendsto_of_leaves (F f ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => log N * refinedSum ω N i) evenAtTop
        (𝓝 (integralTerms F f ω i)) := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · have h := split_tendsto _ _ _ _ _ pair_low_tendsto pair_high_tendsto
    unfold refinedSum
    simp only [if_pos rfl]
    exact h
  · have h := split_tendsto _ _ _ _ _ (quad13_low_tendsto ω hω) (quad13_high_tendsto ω hω)
    unfold refinedSum
    simp only [show (10 : Fin 12) ≠ 8 by decide, ↓reduceIte]
    exact h
  · have h := split_tendsto _ _ _ _ _ (quad14_low_tendsto ω hω) (quad14_high_tendsto ω hω)
    unfold refinedSum
    simp only [show (11 : Fin 12) ≠ 8 by decide, ↓reduceIte]
    exact h

end LeanLab.ChenDoubleSieve.Task349.SplitSum
