import LeanLab.ExceptionalSet.MVMajorFinal

/-!
# R-5150: binary Goldbach for one `n` from a pointwise minor arc bound

T3 MOONSHOT route, CLOUD 20261020T0917Z-cloud39, unit U-6253. AI wrote the Lean code. KNOWN in
method, the classical circle method. Not progress on binary Goldbach, which is OPEN.

* `goldbach_of_minor_lt`: in the exact discrete circle method of `MVEstermann.lean`, if the
  minor arc part at `n ≤ x` is smaller in modulus than the major arc part, `n` is a sum of two
  primes. No averaging over `n`.
* `goldbach_of_minor_small`: with `majorPart_gt`, every even `n ∈ (x/2, x]` off the exceptional
  set `G(n) > T` is a Goldbach number as soon as its minor arc part is at most `M x/4`.
  The unknown input is that pointwise minor arc bound, for every `n`.
-/

namespace LeanLab.Routes.R5150

open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov LeanLab.ExceptionalSet.MV LeanLab.ExceptionalSet.MVMajor
open LeanLab.Routes.R0001

/-- A minor arc part smaller than the major arc part makes `n` a Goldbach number. -/
theorem goldbach_of_minor_lt {x n : ℕ} (hn : n ≤ x) (Q : ℝ)
    (h : ‖minorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x))‖ <
      ‖majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x))‖) : IsGoldbachSum n := by
  by_contra hng
  have hzero : majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x)) +
      minorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x)) = 0 := by
    unfold majorPart minorPart
    rw [add_comm, Finset.sum_add_sum_compl, sum_dft_sq]
    by_contra hne
    exact hng (goldbach_of_conv_ne_zero (primeSupported_logPrimes' x) (by unfold Mx; omega)
      (by unfold Mx; omega) (right_ne_zero_of_mul hne))
  rw [eq_neg_of_add_eq_zero_left hzero, norm_neg] at h
  exact lt_irrefl _ h

/-- With the lab's major arc lower bound: off the exceptional set, a minor arc part at most
`M x/4` gives a Goldbach representation of `n`. -/
theorem goldbach_of_minor_small {x n : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQM : 2 * Q ^ 3 < Mx x)
    (hx : 7 ≤ x) (hn2 : x / 2 + 1 ≤ n) (hnx : n ≤ x) (heven : Even n) {E : ℝ}
    (hmaj : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x))
    (hErr : errMV x Q E ≤ (Mx x : ℝ) * x / 16) (hP2 : 2 ≤ ⌊Q⌋₊)
    (hsing : Real.exp 8 * LeanLab.ExceptionalSet.MVMajor.G n / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4)
    (hminor : ‖minorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4) :
    IsGoldbachSum n :=
  goldbach_of_minor_lt hnx Q (lt_of_le_of_lt hminor
    (majorPart_gt hQ hQM hx hn2 hnx heven hmaj hErr hP2 hsing))

/-- vacuity: the minor arc set is not everything; `0` is a major arc frequency for `Q ≥ 1`. -/
example (x : ℕ) : (0 : ZMod (Mx x)) ∉ minorArcs x 1 := by
  unfold minorArcs; rw [Finset.mem_compl, not_not]; exact zero_mem_majorArcs x le_rfl

end LeanLab.Routes.R5150
