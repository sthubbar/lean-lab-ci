/-
Hu 2019, DOI https://doi.org/10.4064/aa190121-10-4, page 194, Lemma 2.3.
Pintz and Ruzsa 2003, Acta Arith. 109, sections 3 and 4, Theorem 2.
Platt and Trudgian, arXiv https://arxiv.org/abs/1404.5669, sections 3 and 4.
Exponential moment split of the unshifted exceptional measure bound.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp577b

open Finset Real MeasureTheory Filter Topology Set
open LeanLab.Hathi2021.Decomp319a LeanLab.Hathi2021.Decomp570b

namespace LeanLab.Hathi2021.Decomp577eLeavesPT

/-- LEAF: Platt and Trudgian sections 3 and 4, the value E of 0.8844473
above 3/4 plus 10 to the minus 10, in the exponential moment form of Pintz
and Ruzsa section 7. Class HARD. CITED-LEFT, Hu P0101 page 194 Lemma 2.3,
Pintz and Ruzsa P0026 display 4.3 and display 7.1. For some t the moment of
exp of t times the norm of the sum of e of 2 to the j x, j below K, is at
most C exp of K psi, with psi minus t lam at most minus E0 log 2. -/
theorem platt_trudgian_moment_certificate :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ ψ : ℝ, 0 ≤ ψ ∧ ∃ E₀ : ℝ, 3 / 4 + 1 / 10 ^ 10 < E₀ ∧
      ψ - t * (PairLinnik.lam : ℝ) ≤ -(E₀ * Real.log 2) ∧ ∃ C : ℝ, ∀ K : ℕ,
        (∫ x in Icc (0 : ℝ) 1,
          Real.exp (t * ‖∑ j ∈ range K, e ((2 : ℝ) ^ j * x)‖)) ≤
            C * Real.exp (K * ψ) := by
  sorry

/-- Pintz and Ruzsa section 4, display 4.5, the periodic change of
variable x to 16 x that moves the Hu sum over 4 to K to the normalized sum
over j below K minus 3. Hu P0101 page 192 definition of G. -/
theorem shifted_moment_eq (t : ℝ) (K : ℕ) (hK : 4 ≤ K) :
    (∫ x in Icc (0 : ℝ) 1,
      Real.exp (t * ‖∑ ν ∈ Icc 4 K, e ((2 : ℝ) ^ ν * x)‖)) =
    ∫ x in Icc (0 : ℝ) 1,
      Real.exp (t * ‖∑ j ∈ range (K - 3), e ((2 : ℝ) ^ j * x)‖) := by
  set F : ℝ → ℝ := fun y => Real.exp (t * ‖∑ j ∈ range (K - 3), e ((2 : ℝ) ^ j * y)‖)
    with hFdef
  have hpt (x : ℝ) : Real.exp (t * ‖∑ ν ∈ Icc 4 K, e ((2 : ℝ) ^ ν * x)‖) = F (16 * x) := by
    have hI : Finset.Icc 4 K = Finset.Ico 4 (K + 1) := rfl
    rw [hFdef, hI, Finset.sum_Ico_eq_sum_range, show K + 1 - 4 = K - 3 by omega]
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [pow_add]; norm_num; ring
  have hcF : Continuous F := by rw [hFdef]; unfold e; fun_prop
  have hper : Function.Periodic F 1 := by
    intro y
    rw [hFdef]
    dsimp only
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_add, mul_one, e_add]
    have he : e ((2 : ℝ) ^ j) = 1 := by
      unfold e
      have harg : 2 * Real.pi * Complex.I * (((2 : ℝ) ^ j : ℝ) : ℂ) =
          (((2 : ℤ) ^ j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I ((2 : ℤ) ^ j)
    rw [he, mul_one]
  simp_rw [hpt]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left F (by norm_num : (16 : ℝ) ≠ 0)]
  have h16 := hper.intervalIntegral_add_zsmul_eq 16 0
    (fun a b => hcF.intervalIntegrable a b)
  simp only [zero_add, zsmul_eq_mul, Int.cast_ofNat, mul_one] at h16
  change _ = ∫ x in (0 : ℝ)..1, F x
  rw [mul_zero, mul_one, h16, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (16 : ℝ) ≠ 0),
    one_mul]

/-- Pintz and Ruzsa section 3, large deviations from exponential moments.
The exponential Markov inequality on the unit interval. -/
theorem exp_markov_unit (g : ℝ → ℝ) (hg : Continuous g) (t a : ℝ) (ht : 0 ≤ t) :
    volume.real (Icc (0 : ℝ) 1 ∩ {x | a ≤ g x}) ≤
      Real.exp (-(t * a)) * ∫ x in Icc (0 : ℝ) 1, Real.exp (t * g x) := by
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hint : Integrable (fun x => Real.exp (t * g x)) μ :=
    (by fun_prop : Continuous fun x => Real.exp (t * g x)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (t * g x)).le)) hint
    (Real.exp (t * a))
  have hsub : {x | a ≤ g x} ⊆ {x | Real.exp (t * a) ≤ Real.exp (t * g x)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht)
  have hmeas : MeasurableSet {x | a ≤ g x} := measurableSet_le measurable_const hg.measurable
  have hvol : volume.real (Icc (0 : ℝ) 1 ∩ {x | a ≤ g x}) ≤
      μ.real {x | Real.exp (t * a) ≤ Real.exp (t * g x)} := by
    have h1 : volume.real (Icc (0 : ℝ) 1 ∩ {x | a ≤ g x}) = μ.real {x | a ≤ g x} := by
      simp only [μ, measureReal_def, Measure.restrict_apply hmeas, Set.inter_comm]
    rw [h1]
    exact measureReal_mono hsub (measure_ne_top _ _)
  have hpos := Real.exp_pos (t * a)
  rw [Real.exp_neg]
  calc
    _ ≤ μ.real {x | Real.exp (t * a) ≤ Real.exp (t * g x)} := hvol
    _ = (Real.exp (t * a))⁻¹ * (Real.exp (t * a) *
        μ.real {x | Real.exp (t * a) ≤ Real.exp (t * g x)}) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

/-- Hu page 194. Two to the power L is n divided by log n. -/
theorem exp_L_mul_log_two (n : ℕ) (hn : 3 ≤ n) :
    Real.exp (L n * Real.log 2) = (n : ℝ) / Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold L Decomp115.logScale
  rw [div_mul_cancel₀ _ h2.ne', Real.exp_log (div_pos hnpos hlogpos)]

/-- Hu page 194 Lemma 2.3. CONDITIONAL ON the Platt and Trudgian moment
certificate and the periodic shift; the exponential Markov step is proved. -/
theorem platt_trudgian_unshifted_bound_of_leaves :
    ∃ E : ℝ, 3 / 4 + 1 / 10 ^ 10 < E ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∃ N₀ : ℕ, ∀ n₁ : ℕ, N₀ ≤ n₁ →
        volume.real (exceptionalSlice n₁ 0) ≤ K * (n₁ : ℝ) ^ (-E) := by
  obtain ⟨t, ht, ψ, hψ, E₀, hE₀, hgap, C, hC⟩ := platt_trudgian_moment_certificate
  have hC0 : 1 ≤ C := by
    have h := hC 0
    simp only [range_zero, sum_empty, norm_zero, mul_zero, Real.exp_zero,
      setIntegral_const, smul_eq_mul, mul_one, CharP.cast_eq_zero, zero_mul] at h
    simpa [Real.volume_real_Icc] using h
  set E : ℝ := (E₀ + (3 / 4 + 1 / 10 ^ 10)) / 2 with hEdef
  have hE : 3 / 4 + 1 / 10 ^ 10 < E := by rw [hEdef]; linarith
  set δ : ℝ := (E₀ - (3 / 4 + 1 / 10 ^ 10)) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hEδ : E = E₀ - δ := by rw [hEdef, hδdef]; ring
  have hz : Tendsto (fun x : ℝ => Real.log x ^ E₀ / x ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop E₀ hδ).tendsto_div_nhds_zero
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    ((hz.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (tendsto_L_atTop.eventually_ge_atTop 4)
  refine ⟨E, hE, C, by linarith, max 3 (max N₁ N₂), ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hL4 : 4 ≤ L n := hN₂ n (((le_max_right _ _).trans (le_max_right _ _)).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  set K : ℕ := ⌊L n⌋₊ with hKdef
  have hK4 : 4 ≤ K := by
    rw [hKdef]; exact (Nat.le_floor_iff (by linarith)).2 (by exact_mod_cast hL4)
  have hKL : ((K - 3 : ℕ) : ℝ) ≤ L n :=
    (Nat.cast_le.mpr (Nat.sub_le K 3)).trans (Nat.floor_le (by linarith))
  have hcont : Continuous fun x => ‖G n x‖ := by unfold G e; fun_prop
  have hmk := exp_markov_unit (fun x => ‖G n x‖) hcont t
    ((PairLinnik.lam : ℝ) * L n) ht
  have hslice : exceptionalSlice n 0 =
      Icc (0 : ℝ) 1 ∩ {x | (PairLinnik.lam : ℝ) * L n ≤ ‖G n x‖} := by
    ext x; simp [exceptionalSlice]
  have hmom : (∫ x in Icc (0 : ℝ) 1, Real.exp (t * ‖G n x‖)) ≤
      C * Real.exp (((K - 3 : ℕ) : ℝ) * ψ) := by
    have h := shifted_moment_eq t K hK4
    unfold G
    rw [← hKdef, h]
    exact hC (K - 3)
  have hstep : volume.real (exceptionalSlice n 0) ≤
      C * Real.exp (-(E₀ * Real.log 2) * L n) := by
    rw [hslice]
    calc
      _ ≤ Real.exp (-(t * ((PairLinnik.lam : ℝ) * L n))) *
          ∫ x in Icc (0 : ℝ) 1, Real.exp (t * ‖G n x‖) := hmk
      _ ≤ Real.exp (-(t * ((PairLinnik.lam : ℝ) * L n))) *
          (C * Real.exp (((K - 3 : ℕ) : ℝ) * ψ)) :=
        mul_le_mul_of_nonneg_left hmom (Real.exp_pos _).le
      _ = C * Real.exp (((K - 3 : ℕ) : ℝ) * ψ - t * ((PairLinnik.lam : ℝ) * L n)) := by
        rw [Real.exp_sub, Real.exp_neg]; ring
      _ ≤ C * Real.exp (L n * ψ - t * ((PairLinnik.lam : ℝ) * L n)) := by
        gcongr
      _ = C * Real.exp ((ψ - t * (PairLinnik.lam : ℝ)) * L n) := by ring_nf
      _ ≤ C * Real.exp (-(E₀ * Real.log 2) * L n) := by
        gcongr
  have hpow : Real.exp (-(E₀ * Real.log 2) * L n) =
      ((n : ℝ) / Real.log n) ^ (-E₀) := by
    rw [show -(E₀ * Real.log 2) * L n = (L n * Real.log 2) * (-E₀) by ring,
      Real.exp_mul, exp_L_mul_log_two n hn3]
  have hlogb : Real.log n ^ E₀ ≤ (n : ℝ) ^ δ := by
    have h := (hN₁ n (((le_max_left _ _).trans (le_max_right _ _)).trans hn)).le
    exact (div_le_one (Real.rpow_pos_of_pos hnpos δ)).1 h
  have hsplit : ((n : ℝ) / Real.log n) ^ (-E₀) =
      Real.log n ^ E₀ * (n : ℝ) ^ (-E₀) := by
    rw [Real.div_rpow hnpos.le hlogpos.le, Real.rpow_neg hlogpos.le, div_eq_mul_inv, inv_inv,
      mul_comm]
  calc
    _ ≤ C * Real.exp (-(E₀ * Real.log 2) * L n) := hstep
    _ = C * (Real.log n ^ E₀ * (n : ℝ) ^ (-E₀)) := by rw [hpow, hsplit]
    _ ≤ C * ((n : ℝ) ^ δ * (n : ℝ) ^ (-E₀)) := by gcongr
    _ = C * (n : ℝ) ^ (-E) := by
      rw [← Real.rpow_add hnpos, hEδ]; congr 2; ring

end LeanLab.Hathi2021.Decomp577eLeavesPT
