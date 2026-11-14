/-
The remaining analytic Rosser input is an explicit upper weight construction.
The original sifted count bound follows by the proved finite model and support bridge.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp506f

namespace LeanLab.KumchevLiu2007.Task506g

open Real Task506b Task506d Task506e Task506f
open scoped BigOperators Topology

/-- LEAF: Kumchev and Liu page 13 Lemma 3.7 and page 17 before display 58.
Iwaniec, Rosser's sieve, DOI 10.4064/aa-36-2-171-202, page 172 Theorem 1
and page 179 formulas 3.4, 3.6 and 3.7. The upper coefficients have absolute
value at most one and vanish above D. Their main sum is at most a constant
times the sieve product, using the uniform dimension two bound stated on
Kumchev and Liu page 17 and the fact that log D over log z tends to infinity.
Primes with zero density are omitted. Strict cutoff endpoints and the closed
product convention cost a fixed factor at large z. CITED weight construction
and uniform dimension estimate. No sequence count or remainder bound is assumed. -/
theorem upper_weights (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, ∀ hn : InH2 n,
      ∃ μ : ℕ → ℝ, BoundingSieve.IsUpperMoebius μ ∧
        (∀ d ∈ (primeProduct X δ n).divisors, Y X ε ^ (1 / 9 : ℝ) < (d : ℝ) → μ d = 0) ∧
        (∀ d ∈ (primeProduct X δ n).divisors, |μ d| ≤ 1) ∧
        (sieveModel X B δ ε n hn).mainSum μ ≤ C * sieveProduct X δ n := by
  sorry

/-- Page 17 display 58, the exact Rosser application from explicit upper weights.
CONDITIONAL ON upper_weights. The finite support and remainder steps are proved. -/
theorem rosser_application_from_weights (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      siftedCount X B δ ε n ≤ C *
        (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := by
  obtain ⟨C, Xw, hC, hw⟩ := upper_weights B δ ε hB hδ hδ1 hε hε1
  obtain ⟨Xp, hp⟩ := Filter.eventually_atTop.mp (rough_support_parameters B ε hB hε)
  refine ⟨C + 1, max Xw Xp, by positivity, ?_⟩
  intro X hX n hn hXn hnle
  obtain ⟨hY, hroot, hz, hcube⟩ := hp X ((le_max_right _ _).trans hX)
  obtain ⟨μ, hupper, hlevel, hbound, hmain⟩ := hw X ((le_max_left _ _).trans hX) n hn
  have hb := sifted_upper_of_weights X B δ ε C n hn hY hroot hz hcube μ hupper hlevel hbound hmain
  have hNV : 0 ≤ primeMass X B ε * sieveProduct X δ n :=
    mul_nonneg (primeMass_nonneg X B ε) (sieveProduct_nonneg X δ n)
  have hR := remainder_nonneg X B ε n
  calc _ ≤ C * (primeMass X B ε * sieveProduct X δ n) + remainder X B ε n := hb
       _ ≤ (C + 1) * (primeMass X B ε * sieveProduct X δ n + remainder X B ε n) := by
         nlinarith [mul_nonneg hC.le hR]

end LeanLab.KumchevLiu2007.Task506g
