import LeanLab.KadiriLumley2014.PsiFormula259
import LeanLab.RamareSaouter2003.Decomp378a

/-!
P0099 pp. 15 and 16, Lemma 4, applied on p. 19 before display 13.
KadiriLumley2014 Task259 already proves the actual polynomial weighted formula.
The present bridge changes its zero indexing to the actual multiplicity index.
The strict base scale suffices for the existing target at X at least ten to the twelfth.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp378d
open Real Chebyshev Smooth L3Zeta Decomp290c Thm4Assembly
open LeanLab.PNTPort.ExplicitPsi1

/-- P0099 p. 19 before display 13. The actual multiplicity-indexed series
is the multiplicity-weighted series already proved in KadiriLumley2014 Task259. -/
theorem zero_series_reindex (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m) (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∑' i : ZI, ∫ t in (0 : ℝ)..1,
      (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
        (i.1 : ℂ) * (fm m t : ℂ)) =
      ∑' ρ : Zall, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
        ∫ t in (0 : ℝ)..1, (((A * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ)) * (fm m t : ℂ) := by
  have hs := Decomp378a.single_scale_summable m A δ hm hA hδ
  rw [hs.tsum_sigma' (fun _ => Summable.of_finite)]
  apply tsum_congr
  intro ρ
  dsimp only
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hi : (∫ t in (0 : ℝ)..1,
      (((A * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ)) / (ρ : ℂ) * (fm m t : ℂ)) =
      (1 / (ρ : ℂ)) * ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ)) * (fm m t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  rw [hi]
  ring

/-- P0099 pp. 15 and 16, Lemma 4 for the polynomial weight at base A above two.
This is a bridge from the existing proved KadiriLumley2014 Task259 formula.
The separate original endpoint target A equal to two is not claimed here. -/
theorem scaled_weight_formula_strict (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m)
    (hA : 2 < A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
      (∫ t in (0 : ℝ)..1, A * (1 + δ * t) * fm m t) -
      (∑' i : ZI, ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
          (i.1 : ℂ) * (fm m t : ℂ)).re -
      ∫ t in (0 : ℝ)..1,
        (Real.log (2 * π) + (1 / 2) *
          Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2)) * fm m t := by
  have hd : 0 < A * δ := mul_pos (by linarith) hδ
  have h := LeanLab.KadiriLumley2014.Task259.integral_psi_explicit (m := m) (by omega) hA hd
  have hlin (t : ℝ) : A + A * δ * t = A * (1 + δ * t) := by ring
  simp_rw [hlin] at h
  change (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
    (∫ t in (0 : ℝ)..1, (A * (1 + δ * t) - Real.log (2 * π)) * fm m t) -
    (∑' ρ : Zall, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
      ∫ t in (0 : ℝ)..1, (((A * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ)) * (fm m t : ℂ)).re -
    (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2) * fm m t) / 2 at h
  rw [← zero_series_reindex m A δ hm hA.le hδ] at h
  have hlogc := LeanLab.KadiriLumley2014.Task259.trivial_log_continuousOn hA hd.le
  simp_rw [hlin] at hlogc
  have hlogi : IntervalIntegrable (fun t : ℝ =>
      Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2) * fm m t) MeasureTheory.volume 0 1 :=
    (hlogc.mul (continuous_fm m).continuousOn).intervalIntegrable_of_Icc zero_le_one
  have hMi : IntervalIntegrable (fun t : ℝ => A * (1 + δ * t) * fm m t) MeasureTheory.volume 0 1 :=
    (continuous_const.mul ((continuous_const.add (continuous_const.mul continuous_id)))).mul
      (continuous_fm m) |>.intervalIntegrable 0 1
  have hCi := ((continuous_fm m).const_mul (Real.log (2 * π))).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have hmain : (∫ t in (0 : ℝ)..1, (A * (1 + δ * t) - Real.log (2 * π)) * fm m t) =
      (∫ t in (0 : ℝ)..1, A * (1 + δ * t) * fm m t) -
        Real.log (2 * π) * ∫ t in (0 : ℝ)..1, fm m t := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub hMi hCi, intervalIntegral.integral_const_mul]
  have hrem : (∫ t in (0 : ℝ)..1,
      (Real.log (2 * π) + (1 / 2) * Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2)) * fm m t) =
      Real.log (2 * π) * (∫ t in (0 : ℝ)..1, fm m t) +
        (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2) * fm m t) / 2 := by
    simp_rw [add_mul, mul_assoc (1 / 2 : ℝ)]
    rw [intervalIntegral.integral_add hCi (hlogi.const_mul (1 / 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hmain] at h
  rw [hrem]
  linarith

/-- P0099 p. 19, exactly the existing weighted_formula_total target.
The existing strict-scale formula suffices at both scales. No cited input remains. -/
theorem weighted_formula_total (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      (∑' i : ZI, zeroTerm m X u i).re -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hδ : 0 < (m : ℝ) * u := mul_pos hm0 hu
  have hX2 : 2 ≤ X := by linarith
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have hXE : 2 ≤ X * Real.exp u := by nlinarith
  have hscale : X ≤ X * Real.exp u := le_mul_of_one_le_right (by linarith) he
  have htop := scaled_weight_formula_strict m (X * Real.exp u) (m * u) hm (by linarith : 2 < X * Real.exp u) hδ
  have hbot := scaled_weight_formula_strict m X (m * u) hm (by linarith : 2 < X) hδ
  have hzero := Decomp378a.zero_series_difference m X u hm hX hu hmu
  have hlog := Decomp359d.log_integral_difference m X u hm hX hu hmu
  have hf : ContinuousOn (fm m) (Set.uIcc (0 : ℝ) 1) := (continuous_fm m).continuousOn
  have hItop := ((psi_affine_mono (c := X * Real.exp u) (by positivity) hδ.le).intervalIntegrable
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)).mul_continuousOn hf
  have hIbot := ((psi_affine_mono (c := X) (by linarith) hδ.le).intervalIntegrable
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)).mul_continuousOn hf
  have hpsi : (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1, ψ (X * Real.exp u * (1 + m * u * t)) * fm m t) -
      ∫ t in (0 : ℝ)..1, ψ (X * (1 + m * u * t)) * fm m t := by
    rw [← intervalIntegral.integral_sub hItop hIbot]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Dψ, sub_mul]
  have hmain : (∫ t in (0 : ℝ)..1,
      (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) =
      (∫ t in (0 : ℝ)..1, X * Real.exp u * (1 + m * u * t) * fm m t) -
      ∫ t in (0 : ℝ)..1, X * (1 + m * u * t) * fm m t := by
    rw [← intervalIntegral.integral_sub
      (by apply Continuous.intervalIntegrable; exact Continuous.mul (by fun_prop) (continuous_fm m))
      (by apply Continuous.intervalIntegrable; exact Continuous.mul (by fun_prop) (continuous_fm m))]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hpsi, hmain]
  linarith


end LeanLab.RamareSaouter2003.Decomp378d

#print axioms LeanLab.RamareSaouter2003.Decomp378d.zero_series_reindex

#print axioms LeanLab.RamareSaouter2003.Decomp378d.scaled_weight_formula_strict

#print axioms LeanLab.RamareSaouter2003.Decomp378d.weighted_formula_total
