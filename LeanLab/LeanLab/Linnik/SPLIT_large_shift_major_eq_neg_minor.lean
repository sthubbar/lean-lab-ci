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

/-- The real part of the additive character. -/
private lemma e_re_eq_cos (y : ℝ) :
    (LeanLab.PNTPort.LargeSieve.e y).re = Real.cos (2 * Real.pi * y) := by
  unfold LeanLab.PNTPort.LargeSieve.e
  rw [show Complex.I * ((2 * Real.pi * y : ℝ) : ℂ) = ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I
    by ring,
    Complex.exp_ofReal_mul_I_re]

/-- The real part of the additive character is even. -/
private lemma e_neg_re (y : ℝ) :
    (LeanLab.PNTPort.LargeSieve.e (-y)).re = (LeanLab.PNTPort.LargeSieve.e y).re := by
  rw [e_re_eq_cos, e_re_eq_cos, show 2 * Real.pi * (-y) = -(2 * Real.pi * y) by ring,
    Real.cos_neg]

/-- A real scalar in front of a complex number passes through the real part. -/
private lemma ofReal_mul_re (r : ℝ) (z : ℂ) : (((r : ℂ) * z).re) = r * z.re := by
  simp [Complex.mul_re]

/-- The real part of a natural number coerced to `ℂ`. -/
private lemma natCast_re (m : ℕ) : ((m : ℂ)).re = (m : ℝ) := by
  simp

/-- The correlation kernel is continuous. -/
private lemma continuous_kernel (N : ℕ) (n : ℤ) :
    Continuous fun α : ℝ => ‖Sg N α‖ ^ 2 *
      (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re := by
  have he : Continuous fun α : ℝ => (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)).re := by
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  exact (LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2 |>.mul he

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
  classical
  have hpoint (α : ℝ) :
      ‖Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re =
        (((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e
          ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) * α : ℝ)).re := by
    rw [ofReal_mul_re]
    congr 1
    rw [show ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) : ℝ) * α =
      -((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α) by push_cast; ring]
    exact (e_neg_re _).symm
  have hcont : Continuous fun α : ℝ =>
      ((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e
        ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) * α : ℝ) := by
    have he : Continuous fun α : ℝ => LeanLab.PNTPort.LargeSieve.e
        ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) * α : ℝ) := by
      unfold LeanLab.PNTPort.LargeSieve.e
      fun_prop
    exact (Complex.continuous_ofReal.comp
      ((LeanLab.Linnik.U7206.continuous_Sg N).norm.pow 2)).mul he
  simp_rw [hpoint]
  have hstep : (∫ α in Set.Icc (0 : ℝ) 1,
      (((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e
        ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) * α : ℝ)).re) =
      ((∫ α in Set.Icc (0 : ℝ) 1,
        (((‖Sg N α‖ ^ 2 : ℝ) : ℂ) * LeanLab.PNTPort.LargeSieve.e
          ((-(LeanLab.Linnik.Decomp1532a.dif x) : ℤ) * α : ℝ)))).re :=
    integral_re hcont.integrableOn_Icc
  rw [hstep, prime_pair_fourier_identity N (-(LeanLab.Linnik.Decomp1532a.dif x)), natCast_re]

/-- LEAF, OPEN. Emptiness half of the support reduction: on the long shift range no such pair
exists, because both primes are at most `N` and so their difference is at most `N` in absolute
value, while the shift exceeds `N`. This is arithmetic on the representation count: the filtered
set is empty by the comparison `|p - q| ≤ N < |dif x|`. -/
theorem large_shift_pair_count_zero (k N : ℕ) (θ : ℝ)
    (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))
    (hx : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    ((#{y ∈ primesLe N ×ˢ primesLe N |
        (y.1 : ℤ) - y.2 = -(LeanLab.Linnik.Decomp1532a.dif x)} : ℕ) : ℝ) = 0 := by
  classical
  have hA : ∀ a ∈ primesLe N, a ≤ N := fun a ha =>
    Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
  have hfalse : ∀ y ∈ primesLe N ×ˢ primesLe N,
      ¬ ((y.1 : ℤ) - y.2 = -(LeanLab.Linnik.Decomp1532a.dif x)) := by
    intro y hy heq
    rw [Finset.mem_product] at hy
    obtain ⟨h1, h2⟩ := hy
    have hb1 : (y.1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hA y.1 h1
    have hb2 : (y.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hA y.2 h2
    have hd : (LeanLab.Linnik.Decomp1532a.dif x : ℤ) = (y.2 : ℤ) - (y.1 : ℤ) := by
      omega
    have hcast : ((LeanLab.Linnik.Decomp1532a.dif x : ℤ) : ℝ) =
        (y.2 : ℝ) - (y.1 : ℝ) := by
      rw [hd]; push_cast; ring
    have hbound : |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) := by
      rw [hcast, abs_le]
      constructor
      · linarith [Nat.cast_nonneg (α := ℝ) y.1]
      · linarith [Nat.cast_nonneg (α := ℝ) y.2]
    linarith
  have hempty : ({y ∈ primesLe N ×ˢ primesLe N |
      (y.1 : ℤ) - y.2 = -(LeanLab.Linnik.Decomp1532a.dif x)} : Finset (ℕ × ℕ)) = ∅ :=
    Finset.filter_false_of_mem hfalse
  rw [hempty]
  simp

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
  exact (continuous_kernel N (LeanLab.Linnik.Decomp1532a.dif x)).integrableOn_Icc


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
