/-
Split of `LeanLab.Linnik.Decomp1532c.large_shift_major_eq_neg_minor`, the second step of the
split in `LeanLab.Linnik.SPLIT_split_large_shift_bound`: the support reduction which says that on the
long shift range `N < |dif x|` the major arc correlation of that shift equals minus its correlation
over the complement of the major arcs.

The argument. Write `F x α` for `‖Sg N α‖ ^ 2 * (e ((dif x : ℝ) * α)).re`, the correlation kernel
of one shift. Two facts give the statement, and neither mentions `majorArcs` in its own right.

The analytic half, `large_shift_correlation_eq_pair_count`: over the whole unit interval the
correlation counts the ordered pairs of primes at most `N` whose difference is the shift, because
`‖Sg N α‖ ^ 2` is the double sum of the phases `e ((p - q) α)` over those primes and the phase
integral over the unit interval picks out exactly the vanishing frequencies. The count is a
cardinality of a filtered product of two finite sets, so nothing infinite is involved.

The arithmetic half, `large_shift_pair_count_zero`: for a shift larger than `N` in absolute value
that count is empty, since `p, q ≤ N` force `|p - q| ≤ N < |dif x|`.

Together they make the full unit interval integral vanish. The remaining step is bookkeeping, done
in the assembly and not by a leaf: the major arc set is measurable and lies inside the unit
interval, so `integral_inter_add_sdiff` splits the full interval integral into the major arc piece
plus the complement piece, and a vanishing total makes one minus the other. The integrability of
the kernel on the unit interval is the third leaf, `large_shift_integrand_integrable`, used only to
apply that splitting lemma.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-12. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.SPLIT_split_large_shift_bound

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- LEAF, OPEN. Orthogonality half of the support reduction: the correlation of one shift over the
whole unit interval is the number of ordered pairs of primes at most `N` whose difference is that
shift, negated. This is an identity about the kernel alone, with no major arc set and no range
condition in it: it expands the squared exponential sum into the double sum of the phases
`e ((p - q) α)` and integrates each phase over the unit interval. -/
theorem large_shift_correlation_eq_pair_count (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :
    (∫ α in Set.Icc (0 : ℝ) 1,
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) =
      ((#{y ∈ primesLe N ×ˢ primesLe N |
          (y.1 : ℤ) - y.2 = -(LeanLab.Linnik.Decomp1532a.dif x)} : ℕ) : ℝ) := by
  sorry

/-- LEAF, OPEN. Emptiness half of the support reduction: on the long shift range no such pair
exists, because both primes are at most `N` and so their difference is at most `N` in absolute
value, while the shift exceeds `N`. This is arithmetic on the representation count: the filtered
set is empty by the comparison `|p - q| ≤ N < |dif x|`. -/
theorem large_shift_pair_count_zero (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))
    (hx : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    ((#{y ∈ primesLe N ×ˢ primesLe N |
        (y.1 : ℤ) - y.2 = -(LeanLab.Linnik.Decomp1532a.dif x)} : ℕ) : ℝ) = 0 := by
  sorry

/-- LEAF, OPEN. Integrability of the correlation kernel on the unit interval, the side condition of
the splitting lemma used in the assembly. The exponential sum `Sg N α` is a finite sum of phases, so
it is continuous, and so is the phase factor of the shift; a continuous function is interval
integrable. No range condition and no major arc set appears here. -/
theorem large_shift_integrand_integrable (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :
    IntegrableOn
      (fun α => ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)
      (Set.Icc (0 : ℝ) 1) := by
  sorry

/-- ASSEMBLY. The support reduction `large_shift_major_eq_neg_minor`, from the three leaves of this
split: the correlation over the whole unit interval counts the matching tuples
(`large_shift_correlation_eq_pair_count`), the long shift range counts none of them
(`large_shift_pair_count_zero`), so that integral vanishes; the measurable major arc set lies in the
unit interval, so `integral_inter_add_sdiff` splits the unit interval integral into the major arc
piece plus the complement piece (`large_shift_integrand_integrable` supplies the side condition), and
a vanishing total gives the major arc piece minus the complement piece. No sorry. -/
theorem large_shift_major_eq_neg_minor_split (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))
    (hx : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    (∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) =
      -(∫ α in Set.Icc (0 : ℝ) 1 \ majorArcs N ((N : ℝ) ^ θ),
        ‖Sg N α‖ ^ 2 *
          (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) := by
  have hfull : (∫ α in Set.Icc (0 : ℝ) 1,
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) = 0 := by
    rw [large_shift_correlation_eq_pair_count k N θ x,
      large_shift_pair_count_zero k N θ x hx]
  have hInt : IntegrableOn
      (fun α => ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)
      (Set.Icc (0 : ℝ) 1) :=
    large_shift_integrand_integrable k N θ x
  have hsplit := integral_inter_add_sdiff
    (s := Set.Icc (0 : ℝ) 1)
    (f := fun α => ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re)
    (measurableSet_majorArcs N ((N : ℝ) ^ θ)) hInt
  have hsub : majorArcs N ((N : ℝ) ^ θ) ⊆ Set.Icc (0 : ℝ) 1 := fun α h => h.1
  rw [Set.inter_eq_right.mpr hsub] at hsplit
  linarith
