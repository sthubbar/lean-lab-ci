import Mathlib
import LeanLab.KadiriLumley2014.PsiParts301
import LeanLab.RamareSaouter2003.Decomp1531a

/-!
P0099 pp. 15 and 16, Lemma 4, and Davenport Chapter 17.
These elementary primitive identities support a proof using the existing psi1 formula.
No explicit zero formula is assumed in this file.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.PsiPrimitive378
open Real Set Filter Chebyshev
open scoped Topology ArithmeticFunction.vonMangoldt
open LeanLab.Dudek2014.Section22

/-- Derived auxiliary for P0099 p. 16, integration by parts.
The positive part of y minus c has right derivative one at and above c,
and right derivative zero below c. -/
theorem ramp_hasDeriv_right (c x : ℝ) :
    HasDerivWithinAt (fun y : ℝ => max (y - c) 0)
      (if c ≤ x then 1 else 0) (Ioi x) x := by
  exact LeanLab.KadiriLumley2014.Task301.positivePart_hasDerivWithinAt_right c x

/-- Derived auxiliary for P0099 p. 16 and the psi1 formula of Davenport Chapter 17.
The finite von Mangoldt primitive has right derivative equal to psi at every positive x,
including prime powers. This retains the jump convention of the actual psi function. -/
theorem psi1_hasDeriv_right (x : ℝ) (hx : 0 < x) :
    HasDerivWithinAt psi1 (ψ x) (Ioi x) x := by
  exact LeanLab.KadiriLumley2014.Task301.psi1_hasDerivWithinAt_right hx

/-- Derived auxiliary for P0099 p. 16, integration by parts with the psi primitive.
The finite von Mangoldt primitive is continuous on every nonnegative compact interval. -/
theorem continuousOn_psi1 (a b : ℝ) (ha : 0 ≤ a) :
    ContinuousOn psi1 (Icc a b) := by
  by_cases hab : a ≤ b
  · exact LeanLab.KadiriLumley2014.Task301.psi1_continuousOn_Icc ha hab
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    exact continuousOn_empty psi1

/-- Derived auxiliary for P0099 p. 16 and Davenport Chapter 17.
For a continuously differentiable real weight vanishing at both endpoints,
weighted psi integration is integration by parts against the actual psi1 primitive.
Right derivatives handle the prime-power jumps without deleting endpoints. -/
theorem weighted_psi_ibp (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (g g' : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hga : g a = 0) (hgb : g b = 0) :
    (∫ y in a..b, ψ y * g y) = -(∫ y in a..b, psi1 y * g' y) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hc : ContinuousOn psi1 (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_psi1 a b (by linarith)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := psi1) (u' := ψ) (v := g) (v' := g') hc hgc.continuousOn
    (fun x hx => psi1_hasDeriv_right x (by
      simp only [min_eq_left hab, max_eq_right hab, Set.mem_Ioo] at hx
      linarith [hx.1]))
    (fun x _ => (hg x).hasDerivWithinAt)
    (Chebyshev.psi_mono.intervalIntegrable) (hg'.intervalIntegrable a b)
  rw [hga, hgb, mul_zero, mul_zero, sub_zero, zero_sub] at hi
  linarith

/-- Derived auxiliary for P0099 pp. 15 and 16, at the affine smoothing scale.
Weighted psi is the negative weighted psi1 derivative integral divided by A delta.
This identity contains no zero sum and no explicit formula citation. -/
theorem scaled_psi_ibp (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m) (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * Smooth.fm m t) =
      -(1 / (A * δ)) * ∫ t in (0 : ℝ)..1,
        psi1 (A * (1 + δ * t)) * iteratedDeriv 1 (Smooth.fm m) t := by
  have hd : 0 < A * δ := mul_pos (by linarith) hδ
  have h := LeanLab.KadiriLumley2014.Task301.integral_psi_affine_weight
    (m := m) (by omega) (c := A) (d := A * δ) (by linarith) hd
  have hlin (t : ℝ) : A + A * δ * t = A * (1 + δ * t) := by ring
  have hD (t : ℝ) : LeanLab.KadiriLumley2014.Task64.weightD m t =
      iteratedDeriv 1 (Smooth.fm m) t := by
    rw [iteratedDeriv_one]
    exact (LeanLab.KadiriLumley2014.Task64.weight_hasDerivAt m t).deriv.symm
  simp_rw [hlin, hD] at h
  change (A * δ) * (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * Smooth.fm m t) =
    -(∫ t in (0 : ℝ)..1, psi1 (A * (1 + δ * t)) * iteratedDeriv 1 (Smooth.fm m) t) at h
  field_simp
  nlinarith

end LeanLab.RamareSaouter2003.PsiPrimitive378
#print axioms LeanLab.RamareSaouter2003.PsiPrimitive378.ramp_hasDeriv_right
#print axioms LeanLab.RamareSaouter2003.PsiPrimitive378.psi1_hasDeriv_right
#print axioms LeanLab.RamareSaouter2003.PsiPrimitive378.continuousOn_psi1

#print axioms LeanLab.RamareSaouter2003.PsiPrimitive378.weighted_psi_ibp

#print axioms LeanLab.RamareSaouter2003.PsiPrimitive378.scaled_psi_ibp
