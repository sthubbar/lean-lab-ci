/-
Split of the abstract outer Mellin kernel mass estimate `outer_kernel_mass_bound442`
into four steps.

The parent statement bounds the square, over the outer frequency interval from
four over N to one over R, of the absolute log weighted Mellin kernel mass, by a
multiple of the log sixth power times the reciprocal difference kernel at radius
N over R times log cubed N, a multiple of the log seventh power times the
exponentially decaying sum kernel at the same radius, and an additive constant.

The steps below are the elementary route through those magnitudes. First the
weighted mass of the kernel is bounded at every frequency of the outer interval
by one constant times the square root of N times the cube of log N, uniformly in
the frequency and in the radius. Second the square of that mass is interval
integrable in the frequency. Third the frequency integral is bounded by the
length of the interval times that uniform bound, which is where the factor one
over R appears. Fourth the resulting crude product is absorbed by the difference
kernel term, whose radius is large enough to dominate every power of log N that
occurs.

Nothing here changes the statement of `outer_kernel_mass_bound442`; the theorem
`outer_kernel_mass_bound442_split` restates it character for character and proves
it from the four leaves without using the parent theorem.
-/
import LeanLab.Linnik1951.SPLIT_abstract_outer_kernels442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of 4, the pointwise mass bound on the outer interval. There is a
positive constant G such that for N at least three, for every radius R in the
admissible range, and for every frequency α between four over N and one over R,
the absolute Mellin kernel weighted by the cube of the logarithm of N times the
sum of absolute t and two has mass at most G times the square root of N times the
cube of log N. The real part of the Mellin line is at most one for N at least
eight, and the frequency lower bound keeps the imaginary part of the logarithm of
the kernel base away from pi over two by a fixed gap, so the Gamma decay survives
the frequency shift. No square of the mass, no integration over α and no kernel
occurs. -/
theorem outer_kernel_pointwise_mass442 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 3 ≤ N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
      ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
        (∫ t : ℝ,
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
              (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
          G * Real.sqrt (N : ℝ) * Real.log N ^ 3 := by
  sorry

/-- LEAF. Step 2 of 4, the integrability of the squared mass in the frequency.
For N at least three and every admissible radius, the square of the absolute log
weighted Mellin kernel mass is interval integrable over the outer frequency
interval. This is the measure theoretic half of the parent conclusion and
carries no estimate. -/
theorem outer_kernel_mass_sq_intervalIntegrable442 (N : ℕ) (hN : 3 ≤ N)
    (R : ℝ) (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) :
    IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R) := by
  sorry

/-- LEAF. Step 3 of 4, the frequency integral of a uniform bound. Assume the
weighted mass is at most G times the square root of N times the cube of log N at
every frequency of the outer interval, and assume the square of the mass is
interval integrable there. Then the frequency integral of the squared mass is at
most the square of that bound times the length of the interval, written as one
over R minus four over N. This is the monotonicity of the interval integral
against a constant, and it is the only step where the factor one over R is
produced. -/
theorem outer_kernel_mass_constant_integral442 (N : ℕ) (hN : 8 ≤ N)
    (R : ℝ) (hR : 1 ≤ R) (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (G : ℝ) (hG : 0 < G)
    (hmass : ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
        G * Real.sqrt (N : ℝ) * Real.log N ^ 3)
    (hInt : IntervalIntegrable (fun α : ℝ =>
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) volume
      (4 / (N : ℝ)) (1 / R)) :
    (∫ α in (4 / (N : ℝ))..(1 / R),
      (∫ t : ℝ,
        ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
            (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
      G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) := by
  sorry

/-- LEAF. Step 4 of 4, absorption by the difference kernel term. For N at least
three, every admissible radius, and every positive G, the crude bound of step
three is at most one plus the square of G times the log sixth power times the
reciprocal difference kernel at radius N over R times log cubed N, plus the same
multiple of the log seventh power times the sum kernel at that radius, plus one.
The radius is at least one, the difference kernel dominates its own radius there,
and log N is at least one, so the log ninth power supplied by the difference
kernel term covers the log sixth power of the crude bound together with the
factor N over R. The sum kernel term is only used as a nonnegative quantity. -/
theorem outer_kernel_mass_absorb442 (N : ℕ) (hN : 3 ≤ N) (R : ℝ) (hR : 1 ≤ R)
    (hR2 : R ≤ (N : ℝ) ^ (2 / 7 : ℝ)) (G : ℝ) (hG : 0 < G) :
    G ^ 2 * Real.sqrt (N : ℝ) ^ 2 * Real.log N ^ 6 * (1 / R - 4 / (N : ℝ)) ≤
      (G ^ 2 + 1) * Real.log N ^ 6 *
          differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
        (G ^ 2 + 1) * Real.log N ^ 7 *
          sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + (G ^ 2 + 1) := by
  sorry

/-- The parent statement `outer_kernel_mass_bound442`, reassembled from the four
leaves. The constant is one plus the square of the mass constant of step one, and
the threshold is eight so that four over N does not exceed one over R and log N
is at least one. No use of the parent theorem, no sorry. -/
theorem outer_kernel_mass_bound442_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∫ α in (4 / (N : ℝ))..(1 / R),
          (∫ t : ℝ,
            ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
                (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ^ 2) ≤
          C * Real.log N ^ 6 * differenceKernel376 ((N : ℝ) / R * Real.log N ^ 3) +
            C * Real.log N ^ 7 * sumKernel376 ((N : ℝ) / R * Real.log N ^ 3) + C := by
  obtain ⟨G, hG, hmass⟩ := outer_kernel_pointwise_mass442
  refine ⟨G ^ 2 + 1, by positivity, 8, ?_⟩
  intro N hN R hR hR2
  have h3 : 3 ≤ N := by omega
  have hInt := outer_kernel_mass_sq_intervalIntegrable442 N h3 R hR hR2
  have hstep :=
    outer_kernel_mass_constant_integral442 N (by omega) R hR hR2 G hG
      (fun α hα => hmass N h3 R hR hR2 α hα) hInt
  have hbook := outer_kernel_mass_absorb442 N h3 R hR hR2 G hG
  linarith

end LeanLab.Linnik1951
