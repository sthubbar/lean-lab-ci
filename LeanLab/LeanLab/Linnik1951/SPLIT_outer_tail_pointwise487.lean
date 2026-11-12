/-
Unit Linnik1951/SPLIT-outer_tail_pointwise487.
Split of outer_tail_pointwise487 of Decomp487b into the absolute convergence of the
coefficient integral, the cut of the full contour at the moving radius, the norm estimate
on the cut off frequencies, the exponential mass of that remainder and its scalar absorption.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp487b

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Absolute convergence step. For large N the signed coefficient integral along the
line converges absolutely for every alpha, because the line bound is logarithmic in the
frequency and the Gamma factor decays exponentially. This is the finiteness estimate that
lets the full contour be cut. No inequality between the contour and its truncation occurs. -/
theorem outer_tail_integrable487 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ B0 : ℝ, 0 < B0 → ∀ M : ℝ → ℂ,
      LineBound1622 N B0 M → ∀ α : ℝ,
        Integrable (fun t : ℝ => mellinKernel442 N α t * M t) := by
  sorry

/-- LEAF. Cut identity step. The full signed contour minus its truncation at the radius
N over R times log cubed N is exactly the one over two pi times the two frequency tails,
the part above the radius and the part below minus the radius. Only the additivity of the
integral over the three pieces is used; no size estimate occurs. -/
theorem outer_tail_cut_identity487 (N : ℕ) (R α : ℝ) (M : ℝ → ℂ)
    (hT : 0 ≤ (N : ℝ) / R * Real.log N ^ 3)
    (hI : Integrable (fun t : ℝ => mellinKernel442 N α t * M t)) :
    mellinU1622 N M α - truncatedMellin487 N R M α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
          Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
          mellinKernel442 N α t * M t := by
  sorry

/-- LEAF. Triangle inequality step on the cut off frequencies. The norm of the two tail
integrals is at most the line bound constant B0 times the absolute kernel mass carrying the
logarithmic weight of the coefficient bound. No decay and no absorption occurs here. -/
theorem outer_tail_norm_estimate487 (N : ℕ) (R α B0 : ℝ) (M : ℝ → ℂ)
    (hB0 : 0 ≤ B0) (hM : LineBound1622 N B0 M) :
    ‖∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
        Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
        mellinKernel442 N α t * M t‖ ≤
      B0 * ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
        Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
        ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  sorry

/-- LEAF. Exponential mass step on the cut off frequencies. On the outer alpha interval the
scaled kernel decay of the line at radius R gives the two tails the mass a fixed constant
times square root N times N over R cubed times log N to the sixth times the exponential of
minus log N cubed over twenty. This is the quantitative input on the moving complement. -/
theorem outer_tail_complement_mass487 :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 8 ≤ N → ∀ R α : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → α ∈ Set.Icc (4 / (N : ℝ)) (1 / R) →
        ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
          Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
          ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
            Real.exp (-(Real.log N ^ 3 / 20)) := by
  sorry

/-- LEAF. Scalar absorption step. For every positive constant the displayed product, which is
a fixed power of N times log N to the sixth times the exponential of minus log N cubed over
twenty, is at most one once N is large, uniformly in the radius at least one. -/
theorem outer_tail_absorption487 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        C * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20)) ≤ 1 := by
  sorry

/-- The pointwise truncation error of the signed contour at the radius N over R times log
cubed N is eventually at most one on the outer alpha interval, uniformly in the radius and in
every coefficient satisfying the line bound. Proved from the absolute convergence, the cut
identity, the triangle inequality on the cut off frequencies, the exponential mass of that
remainder and its scalar absorption; the two constants are multiplied. -/
theorem outer_tail_pointwise487_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤ 1 := by
  obtain ⟨K, hKpos, hmass⟩ := outer_tail_complement_mass487
  obtain ⟨Ni, hi⟩ := outer_tail_integrable487
  obtain ⟨Na, ha⟩ := outer_tail_absorption487 ((1 / (2 * Real.pi)) * B0 * K)
    (by positivity)
  refine ⟨max 8 (max Ni Na), ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hT0 : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 :=
    mul_nonneg (by positivity) (pow_nonneg hl0 3)
  have hα0 : (0 : ℝ) ≤ α :=
    le_trans (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ)) hα.1
  have hI := hi N hNi B0 hB0 M hM α
  have hcut := outer_tail_cut_identity487 N R α M hT0 hI
  have hnorm := outer_tail_norm_estimate487 N R α B0 M hB0.le hM
  have hm := hmass N hN8 R α hR1 hR hα
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  set I : ℝ := ∫ t in (Set.Ici T ∪ Set.Iic (-T)),
    ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 with hIdef
  change ‖∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ ≤ B0 * I at hnorm
  change I ≤ K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
    Real.exp (-(Real.log N ^ 3 / 20)) at hm
  have hstep : ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤
      (1 / (2 * Real.pi)) * B0 * I := by
    calc ‖mellinU1622 N M α - truncatedMellin487 N R M α‖
        = ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ := by
          rw [hcut]
      _ = (1 / (2 * Real.pi)) *
            ‖∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
      _ ≤ (1 / (2 * Real.pi)) * (B0 * I) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (1 / (2 * Real.pi)) * B0 * I := by ring
  have hstep2 : (1 / (2 * Real.pi)) * B0 * I ≤
      (1 / (2 * Real.pi)) * B0 *
        (K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20))) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hflat : (1 / (2 * Real.pi)) * B0 *
        (K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20))) =
      ((1 / (2 * Real.pi)) * B0 * K) * Real.sqrt N * ((N : ℝ) / R) ^ 3 *
        Real.log N ^ 6 * Real.exp (-(Real.log N ^ 3 / 20)) := by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  have habs := ha N hNa R hR1 hR
  rw [hflat] at *
  linarith
