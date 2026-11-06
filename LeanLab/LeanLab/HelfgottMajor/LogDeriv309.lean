import LeanLab.HelfgottMajor.Gaussian309
import LeanLab.HelfgottMajor.Residue309
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
Local logarithmic derivative factors in the residue calculation of P0014 pages 33 and 34.
The proofs use Mathlib analytic factorization and retain the scale factor from display 4.7.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.LogDeriv309
open Complex Filter
open scoped Topology

/-- The zero at zero of an even nontrivial Dirichlet L function has positive finite order.
This supplies a genuine pole factor in the Laurent calculation on P0014 pages 33 and 34.
-/
theorem even_L_factorization (q : ℕ) [NeZero q] (hq : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      DirichletCharacter.LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ n * u s := by
  let L := DirichletCharacter.LFunction χ
  have ha : ∀ z, AnalyticAt ℂ L z :=
    fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfinite : analyticOrderAt L 0 ≠ ⊤ := by
    intro hh
    have hz : L = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (f := L) (0 : ℂ) ha).mp hh
    have hnon := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (show (1 : ℝ) ≤ (2 : ℂ).re by norm_num)
    exact hnon (congrFun hz 2)
  have hL0 : L 0 = 0 := by
    simpa [L, DirichletCharacter.LFunction, χ.map_zero' hq] using
      ZMod.LFunction_apply_zero_of_even heven.to_fun
  obtain ⟨u, hu, hu0, heq⟩ := (ha 0).analyticOrderAt_ne_top.mp hfinite
  refine ⟨analyticOrderNatAt L 0, ?_, u, hu, hu0, ?_⟩
  · by_contra hn
    have hn0 : analyticOrderNatAt L 0 = 0 := Nat.eq_zero_of_not_pos hn
    have h := heq.self_of_nhds
    simp [hn0, hL0] at h
    exact hu0 h.symm
  · simpa using heq

/-- The regular logarithmic derivative numerator and its derivative at zero.
This is the analytic unit step in the Laurent expansion on P0014 page 33.
-/
theorem regular_logderiv_derivative (n : ℕ) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    HasDerivAt (fun s : ℂ => (n : ℂ) + s * logDeriv u s) (logDeriv u 0) 0 := by
  have hlog : AnalyticAt ℂ (logDeriv u) 0 := hu.deriv.div hu hu0
  simpa using ((hasDerivAt_id (0 : ℂ)).mul hlog.differentiableAt.hasDerivAt).const_add
    (n : ℂ)

/-- The regular logarithmic derivative agrees with s times L prime over L off zero.
Source P0014 page 33, the Laurent expansion after display 4.9.
-/
theorem regular_logderiv_eq (n : ℕ) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    (fun s : ℂ => s * logDeriv (fun z : ℂ => z ^ n * u z) s) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun s => (n : ℂ) + s * logDeriv u s := by
  have hne := hu.continuousAt.tendsto.eventually (eventually_ne_nhds hu0)
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds,
    hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hsa hs0
  change s ≠ 0 at hs0
  rw [logDeriv_fun_mul (f := fun z : ℂ => z ^ n) (g := u) s (pow_ne_zero _ hs0) hs (by fun_prop) hsa.differentiableAt,
    logDeriv_pow]
  field_simp

/-- Scaling the actual Gaussian regular numerator changes the pole coefficient by n log x.
Source P0014 page 33 display 4.7, with the positive order n from the L function factor.
-/
theorem scaled_gaussian_coefficient (n : ℕ) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (x : ℝ) (hx : 0 < x) :
    deriv (fun s : ℂ => ((n : ℂ) + s * logDeriv u s) *
      ((2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1)) * (x : ℂ) ^ s) 0 =
      logDeriv u 0 + n * (((Real.log 2 : ℝ) : ℂ) / 2 -
        (Real.eulerMascheroniConstant : ℂ) / 2) + n * (Real.log x : ℂ) := by
  simpa using (Residue309.scaled_numerator_derivative _ _ (logDeriv u 0)
    (((Real.log 2 : ℝ) : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2)
    n 1 (regular_logderiv_derivative n u hu hu0) Gaussian309.regularized_derivative
    (by simp) Gaussian309.regularized_value x hx).deriv

/-- The actual L function and Gaussian product has the stated regular numerator.
Source P0014 page 33 displays 4.6 and 4.7. The equality is on the positive real approach to zero.
-/
theorem actual_regularized_product (L u : ℂ → ℂ) (n : ℕ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (heq : L =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ n * u s) :
    (fun t : ℝ => (t : ℂ) ^ 2 * logDeriv L (t : ℂ) * Decomp269a.gaussianMellin 0 (t : ℂ))
      =ᶠ[𝓝[>] (0 : ℝ)] fun t =>
        ((n : ℂ) + (t : ℂ) * logDeriv u (t : ℂ)) *
          ((2 : ℂ) ^ ((t : ℂ) / 2) * Gamma ((t : ℂ) / 2 + 1)) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change (t : ℂ) ≠ 0
    exact_mod_cast ht.ne'
  have hl : logDeriv L =ᶠ[𝓝[≠] (0 : ℂ)]
      logDeriv (fun s : ℂ => s ^ n * u s) :=
    (logDeriv_congr_nhds heq).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht.eventually hl, ht.eventually (regular_logderiv_eq n u hu hu0),
    self_mem_nhdsWithin] with t htL htreg htpos
  change 0 < t at htpos
  have hg := Gaussian309.regularized_mellin (t : ℂ) htpos
  rw [← hg, ← htreg, htL]
  ring

/-- A positive pole order forbids a uniform bound for the scaled residue coefficient.
Source P0014 pages 33 and 34. The test scale is exp of a sufficiently large positive real number.
-/
theorem scaled_gaussian_coefficient_unbounded (n : ℕ) (hn : 0 < n) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (B : ℝ) (hB : 0 ≤ B) :
    ∃ x : ℝ, 1 ≤ x ∧
      B < ‖deriv (fun s : ℂ => ((n : ℂ) + s * logDeriv u s) *
        ((2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1)) * (x : ℂ) ^ s) 0‖ := by
  let A : ℂ := logDeriv u 0 + n * (((Real.log 2 : ℝ) : ℂ) / 2 -
    (Real.eulerMascheroniConstant : ℂ) / 2)
  let K : ℝ := B + ‖A‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Real.exp K, Real.one_le_exp_iff.mpr hK.le, ?_⟩
  rw [scaled_gaussian_coefficient n u hu hu0 _ (Real.exp_pos _), Real.log_exp]
  change B < ‖A + (n : ℂ) * (K : ℂ)‖
  have hnorm : ‖(n : ℂ) * (K : ℂ)‖ = (n : ℝ) * K := by
    rw [← ofReal_natCast, ← ofReal_mul, norm_real, Real.norm_of_nonneg (by positivity)]
  have htriangle := norm_sub_le (A + (n : ℂ) * (K : ℂ)) A
  have hid : A + (n : ℂ) * (K : ℂ) - A = (n : ℂ) * (K : ℂ) := by ring
  rw [hid, hnorm] at htriangle
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmul : K ≤ (n : ℝ) * K := by nlinarith
  dsimp [K] at hmul
  linarith

/-- A concrete primitive even nontrivial character for the residue audit on pages 33 and 34.
The quadratic character modulo five makes the factorization hypotheses inhabited.
-/
theorem exists_even_primitive_mod_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.Even := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let χ : DirichletCharacter ℂ 5 :=
    (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
    exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 5) ≠ 2)
  have heven : χ.Even := by
    have hs : quadraticChar (ZMod 5) (-1) = 1 := by
      apply (quadraticChar_one_iff_isSquare (by decide : (-1 : ZMod 5) ≠ 0)).mpr
      exact ⟨2, by decide⟩
    change (Int.castRingHom ℂ) (quadraticChar (ZMod 5) (-1)) = 1
    rw [hs]
    simp
  refine ⟨χ, ?_, hχ, heven⟩
  change DirichletCharacter.conductor χ = 5
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp
    (DirichletCharacter.conductor_dvd_level χ) with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

/-- The scale independent bound for the local residue coefficient is impossible at positive order.
Source P0014 page 33 display 4.7 and page 34. This is a negation of that local uniform bound.
-/
theorem not_uniform_scaled_coefficient_bound (n : ℕ) (hn : 0 < n) (u : ℂ → ℂ)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    ¬ ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖deriv (fun s : ℂ => ((n : ℂ) + s * logDeriv u s) *
        ((2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1)) * (x : ℂ) ^ s) 0‖ ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨x, hx, hgt⟩ := scaled_gaussian_coefficient_unbounded n hn u hu hu0
    (max B 0) (le_max_right _ _)
  have hle := hB x hx
  linarith [le_max_left B 0]

/-- The modulus five character gives an inhabited obstruction in the actual L factorization.
Source P0014 pages 33 and 34. No GRH check or explicit zero sum identity is asserted.
-/
theorem mod_five_residue_scale_obstruction :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.Even ∧
      ∃ n : ℕ, 0 < n ∧ ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (DirichletCharacter.LFunction χ =ᶠ[𝓝 (0 : ℂ)] fun s => s ^ n * u s) ∧
        ¬ ∃ B : ℝ, ∀ x : ℝ, 1 ≤ x →
          ‖deriv (fun s : ℂ => ((n : ℂ) + s * logDeriv u s) *
            ((2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1)) * (x : ℂ) ^ s) 0‖ ≤ B := by
  obtain ⟨χ, hprim, hχ, heven⟩ := exists_even_primitive_mod_five
  obtain ⟨n, hn, u, hu, hu0, heq⟩ := even_L_factorization 5 (by decide) χ hχ heven
  exact ⟨χ, hprim, hχ, heven, n, hn, u, hu, hu0, heq,
    not_uniform_scaled_coefficient_bound n hn u hu hu0⟩

end LeanLab.HelfgottMajor.LogDeriv309
