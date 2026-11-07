/-
Split of the absolute central Mellin kernel mass of Decomp442a.lean.
The parent statement central_kernel_mass442 asks for an integrable
absolute Gamma weighted kernel on the central interval and for its mass
to be at most a constant times square root N times the cube of log N.
The leaves below are the steps of that computation and nothing else:
the modulus of the power factor, the split of a logarithm of a product,
the twisted Gamma mass, the integrability of the weighted kernel, and the
bookkeeping of the constant. central_kernel_mass442_split reassembles
them into the parent statement without using the parent theorem.

The only point of care is the power factor. The base of the kernel power
has real part one over N and imaginary part at most eight pi over N, so
the ratio of its parts is at most eight pi and the imaginary part of its
logarithm is bounded away from pi over two by a fixed gap. That gap is
what keeps the exponential of the Gamma factor away from the Gamma decay,
and it is the reason the mass is finite at all.
-/
import LeanLab.Linnik1951.Decomp442a
import LeanLab.Linnik1951.Gamma442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. First step of the parent proof, the modulus of the power factor.
For N at least two and alpha at most four over N the base of the power has
real part one over N and imaginary part at most eight pi over N, so the
imaginary part of its logarithm is at most pi over two minus one over
sixteen pi; its modulus is at least one over N, and N to the power a half
plus one over log N is at most e times the square root of N. No Gamma
factor, no logarithm of N, no integral here. -/
theorem mellin_base_bound442 (N : ℕ) (α t : ℝ) (hN : 2 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) ^
        (-(mellinLine1622 N t))‖ ≤
      Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) := by
  sorry

/-- LEAF. Second step of the parent proof, the split of the logarithm.
For N at least two the logarithm of N times the sum of absolute t and two
is the sum of two nonnegative logarithms, so its cube is at most eight
cubes of log N plus eight cubes of the logarithm of the sum. -/
theorem log_cube_split442 (N : ℕ) (t : ℝ) (hN : 2 ≤ N) :
    Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3 := by
  sorry

/-- LEAF. Third step of the parent proof, the twisted Gamma mass. The
Gamma factor on the line, weighted by the exponential gap of the power
factor and by the cube of the logarithm of the sum of absolute t and two,
is integrable for every N at least two, and both of its integrals are at
most one constant independent of N and of alpha. This is the analytic core
of the parent proof and the only place where the decay of Gamma is used. -/
theorem gamma_twist_mass442 :
    ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) ∧
      Integrable (fun t : ℝ =>
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        ‖Complex.Gamma (mellinLine1622 N t)‖) ≤ G ∧
      (∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
        (‖Complex.Gamma (mellinLine1622 N t)‖ *
          Real.log (|t| + 2) ^ 3)) ≤ G := by
  sorry

/-- LEAF. Fourth step of the parent proof, the integrability half of the
parent conclusion. The modulus of the kernel times the cube of the
logarithm of N times the sum of absolute t and two is integrable, for N at
least thirty two and alpha at most four over N. This is the first
conjunct of the parent statement on its own, without any estimate of the
integral. -/
theorem kernel_mass_integrable442 (N : ℕ) (α : ℝ) (hN : 32 ≤ N)
    (hα : |α| ≤ 4 / (N : ℝ)) :
    Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
  sorry

/-- LEAF. Fifth step of the parent proof, the bookkeeping of the constant.
For N at least thirty two and a positive constant G, eight e times the
square root of N times the cube of log N times G plus G is at most the
cube of log N times the square root of N times the constant eight e G
times one plus the inverse cube of log two. The last factor absorbs the
additive G because the cube of log N is at least the cube of log two. -/
theorem mass_constant442 (N : ℕ) (G : ℝ) (hN : 32 ≤ N) (hG : 0 < G) :
    8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) ≤
      8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3) * Real.sqrt N *
        Real.log N ^ 3 := by
  sorry

/-- The parent statement central_kernel_mass442, reassembled from the five
leaves above. No use of the parent theorem, no sorry. -/
theorem central_kernel_mass442_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, |α| ≤ 4 / (N : ℝ) →
        Integrable (fun t : ℝ => ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ∧
        (∫ t : ℝ, ‖mellinKernel442 N α t‖ *
          Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
            C * Real.sqrt N * Real.log N ^ 3 := by
  obtain ⟨G, hGpos, hG⟩ := gamma_twist_mass442
  refine ⟨8 * Real.exp 1 * G * (1 + 1 / Real.log 2 ^ 3), ?_, 31, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < 1 + 1 / Real.log 2 ^ 3 := by positivity
    positivity
  intro N hN α hα
  have hN32 : 32 ≤ N := hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  obtain ⟨hAi, hBi, hA, hB⟩ := hG N hN2
  have hdomint : Integrable (fun t : ℝ => 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) := by
    have h1 : Integrable (fun t : ℝ => Real.log N ^ 3 *
        (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖)) := hAi.const_mul _
    exact (h1.add hBi).const_mul _
  have hpoint : ∀ t : ℝ, ‖mellinKernel442 N α t‖ *
      Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖) +
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
    intro t
    have hbase := mellin_base_bound442 N α t hN2 hα
    have hlog := log_cube_split442 N t hN2
    have hk : ‖mellinKernel442 N α t‖ ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ := by
      unfold mellinKernel442
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
    have hpos : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
      have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg t, hNr])
      positivity
    have hf : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt N *
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖ := by positivity
    have h1 := mul_le_mul hk hlog hpos hf
    have hEq : (Real.exp 1 * Real.sqrt N *
          Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            ‖Complex.Gamma (mellinLine1622 N t)‖) *
        (8 * Real.log N ^ 3 + 8 * Real.log (|t| + 2) ^ 3) =
        8 * Real.exp 1 * Real.sqrt N *
          (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖) +
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3)) := by
      ring
    rw [hEq] at h1
    exact h1
  have hval : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) =
      8 * Real.exp 1 * Real.sqrt N *
        (Real.log N ^ 3 * (∫ t : ℝ,
            Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
              ‖Complex.Gamma (mellinLine1622 N t)‖) +
          ∫ t : ℝ, Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
            (‖Complex.Gamma (mellinLine1622 N t)‖ *
              Real.log (|t| + 2) ^ 3)) := by
    rw [integral_const_mul, integral_add (hAi.const_mul _) hBi, integral_const_mul]
  have hub : (∫ t : ℝ, 8 * Real.exp 1 * Real.sqrt N *
      (Real.log N ^ 3 * (Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) +
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ * Real.log (|t| + 2) ^ 3))) ≤
      8 * Real.exp 1 * Real.sqrt N * (Real.log N ^ 3 * G + G) := by
    rw [hval]
    have hc : (0 : ℝ) ≤ 8 * Real.exp 1 * Real.sqrt N := by positivity
    have hl : (0 : ℝ) ≤ Real.log N ^ 3 := pow_nonneg hlogN.le 3
    have h1 : Real.log N ^ 3 * (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          ‖Complex.Gamma (mellinLine1622 N t)‖) ≤ Real.log N ^ 3 * G :=
      mul_le_mul_of_nonneg_left hA hl
    have h2 : (∫ t : ℝ,
        Real.exp (|t| * (Real.pi / 2 - 1 / (16 * Real.pi))) *
          (‖Complex.Gamma (mellinLine1622 N t)‖ *
            Real.log (|t| + 2) ^ 3)) ≤ G := hB
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  exact ⟨kernel_mass_integrable442 N α hN32 hα,
    (integral_mono (kernel_mass_integrable442 N α hN32 hα) hdomint hpoint).trans
      (hub.trans (mass_constant442 N G hN32 hGpos))⟩

end LeanLab.Linnik1951
