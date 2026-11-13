/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, pp. 363 and 364.

ROUTE BURST session 9, 2026-11-12. The end blocks of the split of `Burst8P2.rpart_block_bound`,
the `R` part of one dyadic block, displays 13 and 23 to 27.

The route is the one recorded for `Decomp1624.reduction27A`: display 27 of p. 364 is stated
through the clipped `W`, whose fixed ends `N` and `2N` are not averaged by the integral over
`x`; `Decomp1624` replaced `W` by the averaged `WA`. To reach `WA`, the range `[N, 2N]` of `S`
is replaced by `[a, b]` with `a` and `b` in end blocks of length `K₀ ≈ N L^{-K}`, at a cost
`≪ K₀ L²` by Parseval, and then averaged over `a` and `b`. The two steps of that route were
first stated in this file as leaves; both are now PROVED with the same statements:
`parseval_cost_proved` in `Burst9Parseval.lean` and `clip_average_proved` in
`Burst9Clip5.lean`, and the leaf statements were removed from this file, new in this session.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst8P2b
import LeanLab.PerelliPintz1992.Burst9Display13
import LeanLab.PerelliPintz1992.Burst9Gallagher

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

/-- The left end block `N ≤ a < N + K₀`. -/
def Aset (N K0 : ℕ) : Finset ℕ := Finset.Ico N (N + K0)

/-- The right end block `2N - K₀ < b ≤ 2N`. -/
def Bset (N K0 : ℕ) : Finset ℕ := Finset.Ioc (2 * N - K0) (2 * N)

end
end LeanLab.PerelliPintz1992.Burst9
