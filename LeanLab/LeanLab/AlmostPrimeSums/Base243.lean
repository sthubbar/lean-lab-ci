import LeanLab.AlmostPrimeSums.Decomp243a

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Shared finite coefficient definitions and limit assembly for BJS pp. 52 to 54.
The declarations retain their original Decomp243b names and statements.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Decomp243b

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527a LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a

noncomputable section

/-- All primes in the middle interval, including those dividing N.
Dropping the coprimality restriction gives the upper bound in BJS p. 54 equation 173. -/
def middlePrimes (N : ℕ) : Finset ℕ :=
  (range ⌈((N : ℝ) ^ ((1 : ℝ) / 3))⌉₊).filter
    (fun q => q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ))

/-- The upper sieve coefficient summed over the middle primes.
BJS p. 53 equation 170 and p. 54 equation 173 before the prime integral. -/
def primeCoefficient (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ middlePrimes N,
    Fsieve (log (sieveLevel N B / q) / log ((N : ℝ) ^ ((1 : ℝ) / 8))) / ((q : ℝ) - 1)

/-- The unevaluated summed upper sieve main term, including the factor one half.
BJS p. 52 equation 164 and p. 53 equation 170. -/
def summedMain (N : ℕ) (B : ℝ) : ℝ :=
  idealMass N (1 / 8) * primeCoefficient N B / 2

/-- A main term limit and a negligible error give an eventual upper bound.
Derived limit argument used after BJS p. 54 equation 174. -/
theorem upper_from_limits (a e m v : ℕ → ℝ) (c C : ℝ)
    (hm : ∀ᶠ N in atTop, 0 < m N)
    (ha : Tendsto (fun N => a N / m N) atTop (𝓝 c))
    (he : Tendsto (fun N => e N / m N) atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, Even N → v N ≤ a N + C * e N) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
      v N ≤ (c + η) * m N := by
  intro η hη
  have hlim : Tendsto (fun N => (a N + C * e N) / m N) atTop (𝓝 c) := by
    have hh := ha.add (he.const_mul C)
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc] using hh
  have hbound := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right c hη))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hm.and (hbound.and hv))
  refine ⟨N₀, fun N hEven hN => ?_⟩
  obtain ⟨hmN, hlt, hvN⟩ := hN₀ N hN
  exact (hvN hEven).trans ((div_le_iff₀ hmN).mp hlt.le)

end
end LeanLab.AlmostPrimeSums.Decomp243b
