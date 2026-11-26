import LeanLab.LPZ2007.ZeroFamily373
import LeanLab.LPZ2007.Detector407
import LeanLab.LPZ2007.Pseudo407

/-!
Analytic inputs for Jutila 1977 pages 52 to 54, displays 3.2 to 3.7.
DOI https://doi.org/10.7146/math.scand.a-11701.
The fixed auxiliary epsilon is one hundredth. Normalization moves q over phi q
into each evaluation vector and divides the polynomial by log D.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Density637

open Finset Real Complex

attribute [local instance] Classical.propDecidable

/-- Jutila page 54, C of n and chi, with R equal to D to the one hundredth.
The product is psi of gcd n r. Only squarefree r coprime to q occur. -/
noncomputable def pseudo (D : ℝ) (q n : ℕ) : ℝ :=
  ∑ r ∈ (Icc 1 ⌊D ^ (1 / 100 : ℝ)⌋₊).filter (fun r => Squarefree r ∧ Nat.Coprime r q),
    (∏ p ∈ (Nat.gcd n r).primeFactors, (1 - (p : ℝ))) / r

/-- Jutila page 50, display 2.11, the constant detector term.
At n equal to one every pseudcharacter factor equals one. -/
theorem pseudo_one (D : ℝ) (q : ℕ) :
    pseudo D q 1 =
      ∑ r ∈ (Icc 1 ⌊D ^ (1 / 100 : ℝ)⌋₊).filter
        (fun r => Squarefree r ∧ Nat.Coprime r q), (1 : ℝ) / r := by
  simp [pseudo]

/-- Jutila page 50, display 2.9, and page 52, the finite polynomial support.
The parameters are z1 equal to D to the 57 over 100 and Y equal to D to the 28 over 25. -/
noncomputable def support (D : ℝ) : Finset ℕ :=
  (Icc 1 ⌊D ^ (28 / 25 : ℝ) * Real.log D ^ 2⌋₊).filter
    (fun n => D ^ (57 / 100 : ℝ) < (n : ℝ))

/-- Jutila page 50, display 2.9, divided by log D.
The sieve coefficient is the proved data definition from Detector407. -/
noncomputable def coefficient (X H D : ℝ) (n : ℕ) : ℂ :=
  (Detector407.sieveCoefficient (D ^ (57 / 100 : ℝ)) (D ^ (29 / 50 : ℝ)) n : ℂ) *
    (Real.exp (-(n : ℝ) / D ^ (28 / 25 : ℝ)) : ℂ) *
      (n : ℂ) ^ (-(1 - H / Real.log X) : ℂ) / (Real.log D : ℂ)

/-- Jutila pages 53 and 54, display 3.7, the character dependent vector.
The coefficient magnitude q over phi q is included in the vector itself. -/
noncomputable def vector (X H D : ℝ)
    (z : Σ r : ℕ, DirichletCharacter ℂ r × ℂ) (n : ℕ) : ℂ :=
  ((z.1 : ℝ) / z.1.totient : ℂ) * (pseudo D z.1 n : ℂ) * z.2.1 n *
    (n : ℂ) ^ (-(z.2.2 - (1 - H / Real.log X : ℂ)))

/-- Jutila page 52, display 3.3, the positive smoothing weight.
The pseudcharacter factors are retained in the evaluation vectors. -/
noncomputable def window (ξ η : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(n : ℝ) / Real.exp η) - Real.exp (-(n : ℝ) / Real.exp ξ)) / n

/-- Jutila page 52, display 3.3, positivity on the polynomial support. -/
theorem window_pos {ξ η : ℝ} (hξη : ξ < η) {n : ℕ} (hn : 0 < n) :
    0 < window ξ η n := by
  apply div_pos
  · exact Detector407.exponential_window_pos (Real.exp_pos _)
      (Real.exp_lt_exp.mpr hξη) (by exact_mod_cast hn)
  · exact_mod_cast hn

/-- Jutila page 50, display 2.9, every polynomial index is positive. -/
theorem support_pos {D : ℝ} {n : ℕ} (hn : n ∈ support D) : 0 < n := by
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1

/-- Jutila pages 53 and 54, display 3.7, phases chosen before smoothing.
Mathlib supplies unit phases for every complex evaluation, including zero. -/
theorem aligned_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ) :
    ∃ ν : ι → ℂ, (∀ j, ‖ν j‖ = 1) ∧
      (∑ j ∈ s, ν j * F j) = ((∑ j ∈ s, ‖F j‖ : ℝ) : ℂ) := by
  classical
  choose ν hν hF using (fun j => Complex.exists_norm_eq_mul_self (F j))
  refine ⟨ν, hν, ?_⟩
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun j _ => (hF j).symm)

/-- Jutila page 52, displays 3.4 and 3.5, consistent smoothing intervals.
At D at least exp one, their right and left endpoints are strictly ordered. -/
theorem smoothing_parameters {D : ℝ} (hD : Real.exp 1 ≤ D) :
    ∃ ξ η : ℝ,
      (99 / 100 : ℝ) * Real.log (D ^ (57 / 100 : ℝ)) ≤ ξ ∧
      ξ ≤ Real.log (D ^ (57 / 100 : ℝ)) ∧
      Real.log (D ^ (28 / 25 : ℝ) * Real.log D ^ 2) ≤ η ∧
      η ≤ (101 / 100 : ℝ) * Real.log (D ^ (28 / 25 : ℝ) * Real.log D ^ 2) ∧
      ξ < η := by
  have hDp : 0 < D := (Real.exp_pos _).trans_le hD
  have hL : 1 ≤ Real.log D := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hD
  have hLp : 0 < Real.log D := by linarith
  have hloglog : 0 ≤ Real.log (Real.log D) := Real.log_nonneg hL
  have hz : Real.log (D ^ (57 / 100 : ℝ)) = (57 / 100 : ℝ) * Real.log D :=
    Real.log_rpow hDp _
  have hx : Real.log (D ^ (28 / 25 : ℝ) * Real.log D ^ 2) =
      (28 / 25 : ℝ) * Real.log D + 2 * Real.log (Real.log D) := by
    rw [Real.log_mul (by positivity : D ^ (28 / 25 : ℝ) ≠ 0)
      (by positivity : Real.log D ^ 2 ≠ 0), Real.log_rpow hDp, Real.log_pow]
    norm_num
  refine ⟨Real.log (D ^ (57 / 100 : ℝ)),
    Real.log (D ^ (28 / 25 : ℝ) * Real.log D ^ 2), ?_⟩
  rw [hz, hx]
  refine ⟨by nlinarith, le_rfl, le_rfl, by nlinarith, by linarith⟩

/-- LEAF: Jutila pages 50 and 52, Lemma 6 and displays 3.2 to 3.6.
This is the normalized pseudcharacter zero detector for primitive families.
The detector uses the actual sieve polynomial, not arbitrary witness vectors. -/
theorem zero_detector :
    ∃ c : ℝ, 0 < c ∧ ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∀ z ∈ EZero X H T P,
          c ≤ ‖∑ n ∈ support (P ^ 2 * T),
            coefficient X H (P ^ 2 * T) n * vector X H (P ^ 2 * T) z n‖ := by
  sorry

/-- LEAF: Jutila pages 52 to 54, display 3.6 and the integrated residue estimate.
This is the finite Gram consequence of the integrated estimate, after averaging
in displays 3.4 and 3.5 and bounding the coefficient energy by Lemma 4.
The finite energy is bounded by the convergent full energy before contour shift.
Pseudo407 supplies only the finite Euler identities. The Mellin shift and
summation of residues across primitive characters remain analytic inputs.
The arbitrary positive c specifies the absorbable error. -/
theorem integrated_residue :
    ∀ c : ℝ, 0 < c → ∃ B : ℝ, 0 < B ∧
      ∀ H T : ℝ, 1 ≤ H → 1 ≤ T → ∃ X0 : ℝ,
      ∀ X P : ℝ, X0 ≤ X → 2 ≤ P → T ≤ P → P ≤ Real.sqrt X →
        ∀ s : Finset (Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
          (∀ z ∈ s, z ∈ EZero X H T P) →
          (∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            (⟨z.1, z.2.1⟩ : Σ r : ℕ, DirichletCharacter ℂ r) = ⟨w.1, w.2.1⟩ →
              1 / Real.log (P ^ 2 * T) ≤ |z.2.2.im - w.2.2.im|) →
        ∀ ν : (Σ r : ℕ, DirichletCharacter ℂ r × ℂ) → ℂ,
          (∀ z, ‖ν z‖ = 1) → ∃ ξ η : ℝ,
          (99 / 100 : ℝ) * Real.log ((P ^ 2 * T) ^ (57 / 100 : ℝ)) ≤ ξ ∧
          ξ ≤ Real.log ((P ^ 2 * T) ^ (57 / 100 : ℝ)) ∧
          Real.log ((P ^ 2 * T) ^ (28 / 25 : ℝ) * Real.log (P ^ 2 * T) ^ 2) ≤ η ∧
          η ≤ (101 / 100 : ℝ) * Real.log
            ((P ^ 2 * T) ^ (28 / 25 : ℝ) * Real.log (P ^ 2 * T) ^ 2) ∧
          ξ < η ∧
            (∑ n ∈ support (P ^ 2 * T),
                ‖coefficient X H (P ^ 2 * T) n‖ ^ 2 / window ξ η n) *
              (∑ z ∈ s, ∑ w ∈ s, ν z * star (ν w) *
                (∑ n ∈ support (P ^ 2 * T), (window ξ η n : ℂ) *
                  vector X H (P ^ 2 * T) z n * star (vector X H (P ^ 2 * T) w n))).re ≤
              B * Real.exp ((15 / 4 : ℝ) * H) * s.card +
                (c ^ 2 / 2) * (s.card : ℝ) ^ 2 := by
  sorry

/-- Jutila page 53, absorption after the integrated inequality.
This purely algebraic step also treats the empty selected family. -/
theorem absorb {J c B E : ℝ} (hJ : 0 ≤ J) (hc : 0 < c) (hBE : 0 ≤ B * E)
    (h : (c * J) ^ 2 ≤ B * E * J + (c ^ 2 / 2) * J ^ 2) :
    J ≤ (2 * B / c ^ 2) * E := by
  by_cases hzero : J = 0
  · subst J
    rw [div_mul_eq_mul_div]
    exact div_nonneg (by nlinarith) (sq_nonneg c)
  · have hJpos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hzero)
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    have hprod : (c ^ 2 * J - 2 * B * E) * J ≤ 0 := by nlinarith [h]
    have hbound : c ^ 2 * J - 2 * B * E ≤ 0 :=
      nonpos_of_mul_nonpos_left hprod hJpos
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith

end LeanLab.LPZ2007.Density637

#print axioms LeanLab.LPZ2007.Density637.pseudo
#print axioms LeanLab.LPZ2007.Density637.support
#print axioms LeanLab.LPZ2007.Density637.coefficient
#print axioms LeanLab.LPZ2007.Density637.vector
#print axioms LeanLab.LPZ2007.Density637.window
#print axioms LeanLab.LPZ2007.Density637.window_pos
#print axioms LeanLab.LPZ2007.Density637.zero_detector
#print axioms LeanLab.LPZ2007.Density637.integrated_residue
#print axioms LeanLab.LPZ2007.Density637.absorb

#print axioms LeanLab.LPZ2007.Density637.support_pos

#print axioms LeanLab.LPZ2007.Density637.aligned_sum

#print axioms LeanLab.LPZ2007.Density637.smoothing_parameters

#print axioms LeanLab.LPZ2007.Density637.pseudo_one
