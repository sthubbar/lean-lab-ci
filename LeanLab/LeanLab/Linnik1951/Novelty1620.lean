import LeanLab.Linnik1951.Conventions

/-!
# Linnik 1951, Novelty1620: powers of two with small exponents

AI wrote this Lean code, unit U-1620, run 20261105T0803Z-23816. Binary Goldbach is OPEN.
Tag: ORIGINAL CANDIDATE, the statement shape only. It is a target and nothing here proves it.
Source of the claim: research/novelty/Linnik1951-20261102T1240Z.md, section 6 Result 5.
Literature search recorded in TRIAGE-U1620-20261105: no prior statement found in four web searches and
in the three nearest papers, Li and Liu 2610.15784, Johnston and Trudgian 2605.17825, Heath-Brown and
Puchta math/0201299. That search is small, so the tag stays CANDIDATE, not ORIGINAL.
Numeric test: scripts/linnik_counts.py, no failure among even N in [2^21, 2^22] at θ = 0.55 and 0.6.
That test is finite and says nothing about large N.
-/

namespace LeanLab.Linnik1951.Novelty1620

open LeanLab.Linnik LeanLab.DERZ1997

/-- `N = p + q + 2^{ν₁} + … + 2^{ν_k}` with primes `p, q`, every `ν i ≥ 1`, every `2^{ν i} ≤ N^θ`.
Twin: `N` is a sum of two primes and exactly `k` powers of two, each power at most `N^θ`. -/
def LowBitsRep (θ : ℝ) (k N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin k → ℕ,
    (∀ i, 1 ≤ ν i ∧ (2 : ℝ) ^ ν i ≤ (N : ℝ) ^ θ) ∧ N = p + q + ∑ i, 2 ^ ν i

/-- A restricted representation is a representation of Linnik's kind. -/
theorem lowBitsRep_exact {θ : ℝ} {k N : ℕ} (h : LowBitsRep θ k N) : LinnikExact k N := by
  obtain ⟨p, q, hp, hq, ν, hν, hN⟩ := h
  exact ⟨p, q, hp, hq, ν, fun i => (hν i).1, hN⟩

/-- Vacuity instance for `LowBitsRep` at a θ in the range: `16 = 7 + 7 + 2^1` and `2 ≤ 16^(3/4) = 8`. -/
theorem lowBitsRep_instance : LowBitsRep (3 / 4) 1 16 := by
  have h8 : ((16 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) = 8 := by
    have h : ((16 : ℕ) : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨7, 7, by norm_num, by norm_num, fun _ => 1, fun _ => ⟨le_rfl, ?_⟩, by simp⟩
  rw [h8]
  norm_num

/-- LEAF. OPEN. Unit U-1620. Twin: assume GRH. For every real θ with 1/2 < θ < 1 there is `k₀` such that
for every `k ≥ k₀`, every sufficiently large even `N` is two primes plus exactly `k` powers of two, each
power at most `N^θ`. So `N` reaches a Goldbach number by changing about `k` of its low θ log₂ N bits.
Source of the claim: research/novelty/Linnik1951-20261102T1240Z.md section 6 Result 5. Compare P0093 page
154, equation 2.1, where the exponents are free. Route to try: pages 164 and 165, Lemmas 4 and 5, where
the measure bound `N^{ε(η) - 1}` for the set where `|T|` is large must be redone for a sum of θ log₂ N
terms, and it can then be no smaller than about `N^{-θ}`. GRH is not satisfiable here by an instance;
`lowBitsRep_instance` shows the conclusion's predicate holds at one point. -/
theorem linnik_low_bits (_hG : GRH) :
    ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → AllLargeEven (LowBitsRep θ k) := by
  sorry

end LeanLab.Linnik1951.Novelty1620

#print axioms LeanLab.Linnik1951.Novelty1620.lowBitsRep_exact
#print axioms LeanLab.Linnik1951.Novelty1620.lowBitsRep_instance
