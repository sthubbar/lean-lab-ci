import LeanLab.RamareSaouter2003.Decomp378d

/-!
P0099 pp. 15 and 16, the base-two endpoint of the corrected Lemma 4.
The existing Task259 proof uses a geometric majorant on y above two.
A four-ninths majorant on y above three halves includes the missing endpoint.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp378e
open Real Set MeasureTheory Smooth L3Zeta Thm4Assembly Chebyshev
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.PNTPort.ExplicitPsi1.Trivial
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task301
open LeanLab.KadiriLumley2014.Task259
open LeanLab.Dudek2014.Section22 (psi1)

/-- Derived endpoint auxiliary for P0099 p. 16.
On y above three halves, each differentiated trivial-zero term is bounded by
four ninths to the n plus one, a summable geometric majorant. -/
theorem trivial_derivative_bound_half (n : ℕ) {y : ℝ} (hy : 3 / 2 < y) :
    ‖-y ^ (-2 * ((n : ℝ) + 1)) / (2 * n + 2)‖ ≤
      (4 / 9 : ℝ) ^ (n + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [norm_div, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (by positivity), negative_even_rpow (by linarith)]
  have hq : 1 / y ^ 2 ≤ (4 / 9 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < y ^ 2)).mpr
    nlinarith
  calc
    _ ≤ (1 / y ^ 2) ^ (n + 1) := div_le_self (by positivity) (by linarith)
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hq _

/-- Derived endpoint auxiliary for P0099 pp. 15 and 16.
The integrated trivial-zero series has the required logarithmic derivative
at every y at least two, including y equal to two. -/
theorem hasDerivAt_trivial_series_ge_two {y : ℝ} (hy : 2 ≤ y) :
    HasDerivAt (fun y : ℝ => y * ∑' n : ℕ, tb y n)
      (Real.log (1 - 1 / y ^ 2) / 2) y := by
  have hs : Summable (fun n : ℕ => (4 / 9 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_abs_lt_one (by norm_num : |(4 / 9 : ℝ)| < 1)).mul_right (4 / 9)
  have hd := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi
    (convex_Ioi (3 / 2 : ℝ)).isPreconnected
    (fun n z hz => hasDerivAt_y_tb n (by change 3 / 2 < z at hz; linarith))
    (fun n z hz => trivial_derivative_bound_half n hz)
    (show (3 : ℝ) ∈ Ioi (3 / 2 : ℝ) by norm_num)
    ((summable_tb (by norm_num : (1 : ℝ) ≤ 3)).mul_left 3)
    (show y ∈ Ioi (3 / 2 : ℝ) by change 3 / 2 < y; linarith)
  rw [(hasSum_trivial_derivatives (by linarith : 1 < y)).tsum_eq] at hd
  simpa only [tsum_mul_left] using hd

/-- Derived endpoint auxiliary for P0099 p. 16. The logarithmic remainder is continuous at base two. -/
theorem trivial_log_continuousOn_ge_two {c d : ℝ} (hc : 2 ≤ c) (hd : 0 ≤ d) :
    ContinuousOn (fun t : ℝ => Real.log (1 - 1 / (c + d * t) ^ 2)) (Icc 0 1) := by
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 2 ≤ c + d * t := by
    intro t ht
    nlinarith [mul_nonneg hd ht.1]
  have hsq : ∀ t ∈ Icc (0 : ℝ) 1, (c + d * t) ^ 2 ≠ 0 := by
    intro t ht
    have h := hp t ht
    nlinarith
  apply (continuousOn_const.sub (continuousOn_const.div
    (by fun_prop : ContinuousOn (fun t : ℝ => (c + d * t) ^ 2) (Icc 0 1)) hsq)).log
  intro t ht
  have h := hp t ht
  have hpos : 0 < (c + d * t) ^ 2 := by nlinarith
  apply ne_of_gt
  apply sub_pos.mpr
  exact (div_lt_one hpos).mpr (by nlinarith)


/-- Derived endpoint auxiliary for P0099 p. 16. Integration by parts for the trivial-zero remainder includes base two. -/
theorem integral_trivial_weightD_ge_two {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 2 ≤ c) (hd : 0 ≤ d) :
    (∫ t in (0 : ℝ)..1,
      ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) =
      -(d / 2) * (∫ t in (0 : ℝ)..1,
        Real.log (1 - 1 / (c + d * t) ^ 2) * weight m t) := by
  let F : ℝ → ℝ := fun t => (c + d * t) * ∑' n : ℕ, tb (c + d * t) n
  have hp : ∀ t ∈ uIcc (0 : ℝ) 1, 2 ≤ c + d * t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    nlinarith [mul_nonneg hd ht.1]
  have hFd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F ((d / 2) * Real.log (1 - 1 / (c + d * t) ^ 2)) t := by
    intro t ht
    have hlin : HasDerivAt (fun t : ℝ => c + d * t) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).const_add c
    convert (hasDerivAt_trivial_series_ge_two (hp t ht)).comp t hlin using 1
    · rfl
    · ring
  have hFc : ContinuousOn F (uIcc (0 : ℝ) 1) :=
    fun t ht => (hFd t ht).continuousAt.continuousWithinAt
  have hlog := trivial_log_continuousOn_ge_two hc hd
  rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hlog
  have hdi : IntervalIntegrable (fun t : ℝ => (d / 2) * Real.log (1 - 1 / (c + d * t) ^ 2)) volume 0 1 :=
    (hlog.const_mul (d / 2)).intervalIntegrable
  have hwd := (weightD_continuous m).intervalIntegrable (μ := volume) 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hFc (weight_continuous m).continuousOn
    (fun t ht => hFd t (by simpa using mem_Icc_of_Ioo ht))
    (fun t _ => weight_hasDerivAt m t) hdi hwd
  rw [(weight_endpoints hm).1, (weight_endpoints hm).2] at h
  simp only [mul_zero, sub_self, zero_sub] at h
  change (∫ t in (0 : ℝ)..1, F t * weightD m t) = _
  rw [h]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- P0099 pp. 15 and 16. The existing psi-one transfer proof now includes the base-two endpoint. -/
theorem integral_psi_explicit_ge_two {m : ℕ} (hm : 0 < m) {c d : ℝ}
    (hc : 2 ≤ c) (hd : 0 < d) :
    (∫ t in (0 : ℝ)..1, Chebyshev.psi (c + d * t) * weight m t) =
      (∫ t in (0 : ℝ)..1, ((c + d * t) - Real.log (2 * π)) * weight m t) -
      (∑' ρ : Zall,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
          (∫ t in (0 : ℝ)..1, ((c + d * t : ℝ) : ℂ) ^ (ρ : ℂ) *
            (weight m t : ℂ))).re -
      (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (c + d * t) ^ 2) * weight m t) / 2 := by
  have hc0 : 0 < c := by linarith
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, 2 ≤ c + d * t := by
    intro t ht
    nlinarith [mul_nonneg hd.le ht.1]
  have hZc : ContinuousOn (fun t : ℝ => Zreal (c + d * t)) (Icc 0 1) := by
    unfold Zreal
    exact Complex.continuous_re.comp_continuousOn
      ((by fun_prop : ContinuousOn (fun t : ℝ => ((c + d * t : ℝ) : ℂ)) (Icc 0 1)).mul
        (continuousOn_zterm_sum hc0 hd.le))
  have hTc : ContinuousOn (fun t : ℝ => (c + d * t) * ∑' n : ℕ, tb (c + d * t) n) (Icc 0 1) := by
    intro t ht
    exact (ContinuousAt.comp (f := fun s : ℝ => c + d * s) (x := t)
      (hasDerivAt_trivial_series_ge_two (hp t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => c + d * t) t)).continuousWithinAt
  have hwd : ContinuousOn (weightD m) (Icc (0 : ℝ) 1) := (weightD_continuous m).continuousOn
  have hZi : IntervalIntegrable (fun t : ℝ => Zreal (c + d * t) * weightD m t) volume 0 1 :=
    (hZc.mul hwd).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hTi : IntervalIntegrable (fun t : ℝ => ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) volume 0 1 :=
    (hTc.mul hwd).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hMi := (by unfold weightD; fun_prop : Continuous (fun t : ℝ =>
    ((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t)).intervalIntegrable (μ := volume) 0 1
  have hCi := ((weightD_continuous m).const_mul
    ((deriv riemannZeta (-1) / riemannZeta (-1)).re)).intervalIntegrable (μ := volume) 0 1
  have hform : (∫ t in (0 : ℝ)..1, psi1 (c + d * t) * weightD m t) =
      (∫ t in (0 : ℝ)..1,
        ((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t) -
      (∫ t in (0 : ℝ)..1, Zreal (c + d * t) * weightD m t) -
      (∫ t in (0 : ℝ)..1, ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
        ((((c + d * t) ^ 2 / 2 - (c + d * t) * Real.log (2 * π)) * weightD m t -
          Zreal (c + d * t) * weightD m t) +
          (deriv riemannZeta (-1) / riemannZeta (-1)).re * weightD m t) -
          ((c + d * t) * ∑' n : ℕ, tb (c + d * t) n) * weightD m t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        dsimp only
        rw [psi1_formula (by linarith [hp t ht])]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hMi.sub hZi).add hCi) hTi,
          intervalIntegral.integral_add (hMi.sub hZi) hCi,
          intervalIntegral.integral_sub hMi hZi,
          intervalIntegral.integral_const_mul, integral_weightD_zero hm]
        ring
  have htransfer := integral_psi_affine_weight hm hc0 hd
  rw [hform, integral_main_weightD hm c d,
    integral_Zreal_weightD hm hc0 hd.le, integral_trivial_weightD_ge_two hm hc hd.le] at htransfer
  apply (mul_left_cancel₀ hd.ne')
  nlinarith [htransfer]

/-- P0099 pp. 15 and 16, corrected Lemma 4. Exactly the original scaled_weight_formula target, including A equal to two. -/
theorem scaled_weight_formula (m : ℕ) (A δ : ℝ) (hm : 2 ≤ m)
    (hA : 2 ≤ A) (hδ : 0 < δ) :
    (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
      (∫ t in (0 : ℝ)..1, A * (1 + δ * t) * fm m t) -
      (∑' i : ZI, ∫ t in (0 : ℝ)..1,
        (((A * (1 + δ * t) : ℝ) : ℂ) ^ (i.1 : ℂ)) /
          (i.1 : ℂ) * (fm m t : ℂ)).re -
      ∫ t in (0 : ℝ)..1,
        (Real.log (2 * π) + (1 / 2) *
          Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2)) * fm m t := by
  have hd : 0 < A * δ := mul_pos (by linarith) hδ
  have h := integral_psi_explicit_ge_two (m := m) (by omega) hA hd
  have hlin (t : ℝ) : A + A * δ * t = A * (1 + δ * t) := by ring
  simp_rw [hlin] at h
  change (∫ t in (0 : ℝ)..1, ψ (A * (1 + δ * t)) * fm m t) =
    (∫ t in (0 : ℝ)..1, (A * (1 + δ * t) - Real.log (2 * π)) * fm m t) -
    (∑' ρ : Zall, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) / (ρ : ℂ) *
      ∫ t in (0 : ℝ)..1, (((A * (1 + δ * t) : ℝ) : ℂ) ^ (ρ : ℂ)) * (fm m t : ℂ)).re -
    (∫ t in (0 : ℝ)..1, Real.log (1 - 1 / (A * (1 + δ * t)) ^ 2) * fm m t) / 2 at h
  rw [← Decomp378d.zero_series_reindex m A δ hm hA hδ] at h
  have hlogc := trivial_log_continuousOn_ge_two hA hd.le
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


end LeanLab.RamareSaouter2003.Decomp378e

#print axioms LeanLab.RamareSaouter2003.Decomp378e.trivial_derivative_bound_half

#print axioms LeanLab.RamareSaouter2003.Decomp378e.hasDerivAt_trivial_series_ge_two

#print axioms LeanLab.RamareSaouter2003.Decomp378e.trivial_log_continuousOn_ge_two

#print axioms LeanLab.RamareSaouter2003.Decomp378e.integral_trivial_weightD_ge_two

#print axioms LeanLab.RamareSaouter2003.Decomp378e.integral_psi_explicit_ge_two

#print axioms LeanLab.RamareSaouter2003.Decomp378e.scaled_weight_formula
