import LeanLab.GoldbachGaps.Goldston1990Selberg
import LeanLab.GoldbachGaps.Goldston1990Thm6Core

/-!
# Goldston 1990, the Theorem of display 6 in the lab's own definitions

Lab proof, unit U-6300, CLOUD 20261020T1017Z-cloud40, P0030. AI wrote this file. Known
mathematics, Goldston 1990.

`fejer_explicit`: for naturals `1 ≤ K ≤ N`,
`|Σ_{|n| ≤ K} (K - |n|) R(N + n) - K² N| ≤ J(N, K) + 2 K² |θ(N) - N|`
`+ K³ (2 log²(N + K) + 1 + 2 (log N + 1) + 2 (log N + 1)²)`,
with `fejer`, `Rg` and `Jg` exactly as in `Goldston1990Main.lean`, so display 6 with no cited
input and no `O(K N)` term; the prime number theorem enters only through `θ(N) - N`, see
`Goldston1990Thm6PNT.lean`. Proof in `Goldston1990Thm6Core.lean`. Binary Goldbach is OPEN.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset

lemma fejer_eq_fejerC (N K : ℕ) : fejer N K = Thm6.fejerC N K := rfl

/-- **Display 6, explicit.** -/
theorem fejer_explicit (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N) :
    |fejer N K - (K : ℝ) ^ 2 * N| ≤
      Jg N K + 2 * (K : ℝ) ^ 2 * |θ (N : ℝ) - N| +
        (K : ℝ) ^ 3 * (2 * Real.log (N + K) ^ 2 + 1 + 2 * (Real.log N + 1) +
          2 * (Real.log N + 1) ^ 2) := by
  rw [fejer_eq_fejerC, jg_eq_sum (by omega)]
  exact Thm6.fejerC_explicit N K hK hKN

end LeanLab.GoldbachGaps.Goldston1990
