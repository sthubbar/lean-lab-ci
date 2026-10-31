/-
P0095 W. C. Lu 2010, Section 9, p. 2391. Unit U-6846, CLOUD MANUAL-M1, 2026-10-21, track T1.

Section 9 opens "By usual way Σ_{k=-∞}^{∞} |D₂(k)|² = ∫_𝔪 |∫_a^b S(td+d, td, α) S(N-td, N-td-d, α) dt|² dα".
This file PROVES that display, `sec9_parseval`, by Parseval on the period interval of length 1,
`hasSum_sq_fourierCoeffOn`: D₂(k) is the k-th Fourier coefficient of the minor arc part of
H(α) = ∫_a^b S S dt. The Section 9 input then becomes the minor arc L² bound
∫_𝔪 |H|² ≪ N^{3-c+0.00011}, the quantity the paper bounds "as usual" from the minor arc
estimate of [12, p. 107]; `InputsM` cites that bound instead of the sum over k.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Arcs

namespace LeanLab.ExceptionalSet.Lu2010Sec9
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Lemma1
  LeanLab.ExceptionalSet.Lu2010Orth LeanLab.ExceptionalSet.Lu2010Arcs

/-- `H(α) = ∫_a^b S(td+d, td, α) S(N-td, N-td-d, α) dt`. -/
noncomputable def H (N : ℕ) (α : ℝ) : ℂ :=
  ∫ t in Set.Icc (aa N) (bb N),
    Ssum (t * dd N + dd N) (t * dd N) α * Ssum (N - t * dd N) (N - t * dd N - dd N) α

/-- The minor arc part `G = 1_{𝔐ᶜ} H`. -/
noncomputable def G (N : ℕ) : ℝ → ℂ := (major N)ᶜ.indicator (H N)

theorem F_eq (N k : ℕ) (α : ℝ) : F N k α = H N α * ee (-(k * α)) := by
  unfold F H; rw [integral_mul_const]

theorem H_eq_F0 (N : ℕ) : H N = F N 0 := by
  funext α; rw [F_eq]; simp [ee]

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * Complex.I * (x : ℂ) = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `H` is bounded, by the sum of the pair weights. -/
theorem H_bound {N : ℕ} (hN : 0 < N) (α : ℝ) :
    ‖H N α‖ ≤ ∑ n ∈ range (0 + 2 * N + 1), ∑ m ∈ range (0 + 2 * N + 1), |cc N n m| := by
  rw [H_eq_F0, F, inner_eq hN 0 α]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun m _ => ?_))
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- The period: `b - a = 1` for `a = -1/Q`, `b = 1 - 1/Q`. -/
theorem per_len (N : ℕ) : (1 - 1 / QQ N) - (-1 / QQ N) = 1 := by ring

theorem per_lt (N : ℕ) : -1 / QQ N < 1 - 1 / QQ N := by linarith [per_len N]

/-- `D₂(k)` is the `k`-th Fourier coefficient of `G` on the period interval. -/
theorem D2c_eq_coeff {N : ℕ} (k : ℕ) :
    D2c N k = fourierCoeffOn (per_lt N) (G N) (k : ℤ) := by
  rw [fourierCoeffOn_eq_integral _ _ (per_lt N), per_len, div_one, one_smul,
    intervalIntegral.integral_of_le (per_lt N).le]
  unfold D2c G
  rw [show per N \ major N = Set.Ioc (-1 / QQ N) (1 - 1 / QQ N) ∩ (major N)ᶜ from rfl,
    ← setIntegral_indicator (major_measurable N).compl]
  refine setIntegral_congr_fun measurableSet_Ioc (fun α _ => ?_)
  simp only [Set.indicator]
  split_ifs
  · rw [F_eq, fourier_coe_apply, smul_eq_mul, mul_comm]
    congr 1; unfold ee; congr 1; push_cast; ring
  · simp

theorem G_memLp {N : ℕ} (hN : 0 < N) :
    MemLp (G N) 2 (volume.restrict (Set.Ioc (-1 / QQ N) (1 - 1 / QQ N))) := by
  have hH : Continuous (H N) := by rw [H_eq_F0]; exact F_continuous hN 0
  refine MemLp.of_bound ((hH.measurable.indicator (major_measurable N).compl).aestronglyMeasurable)
    (∑ n ∈ range (0 + 2 * N + 1), ∑ m ∈ range (0 + 2 * N + 1), |cc N n m|)
    (Filter.Eventually.of_forall fun α => ?_)
  unfold G
  by_cases h : α ∈ (major N)ᶜ
  · rw [Set.indicator_of_mem h]; exact H_bound hN α
  · rw [Set.indicator_of_notMem h, norm_zero]
    exact Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ => abs_nonneg _

/-- **Section 9, first display, PROVED**: `Σ_{k ∈ ℤ} |D₂(k)|² = ∫_𝔪 |H|²`, as a `HasSum`
over the Fourier coefficients of `G`. -/
theorem sec9_parseval {N : ℕ} (hN : 0 < N) :
    HasSum (fun j : ℤ => ‖fourierCoeffOn (per_lt N) (G N) j‖ ^ 2)
      (∫ α in per N \ major N, ‖H N α‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn (per_lt N) (G_memLp hN)
  rw [per_len, inv_one, one_smul, intervalIntegral.integral_of_le (per_lt N).le] at h
  convert h using 1
  rw [show per N \ major N = Set.Ioc (-1 / QQ N) (1 - 1 / QQ N) ∩ (major N)ᶜ from rfl,
    ← setIntegral_indicator (major_measurable N).compl]
  refine setIntegral_congr_fun measurableSet_Ioc (fun α _ => ?_)
  unfold G
  by_cases hα : α ∈ (major N)ᶜ
  · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]
  · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα]; simp

/-- The window sum is at most the minor arc `L²` integral. -/
theorem sec9_window {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Win N, ‖D2c N k‖ ^ 2 ≤ ∫ α in per N \ major N, ‖H N α‖ ^ 2 := by
  have h := sec9_parseval hN
  have hmap : ∑ k ∈ Win N, ‖D2c N k‖ ^ 2 =
      ∑ j ∈ (Win N).map Nat.castEmbedding, ‖fourierCoeffOn (per_lt N) (G N) j‖ ^ 2 := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl; intro k _
    rw [D2c_eq_coeff]; rfl
  rw [hmap]
  exact sum_le_hasSum _ (fun j _ => by positivity) h

/-- **Cited input**, as `InputsC` but with Section 9 as the minor arc `L²` bound
`∫_𝔪 |H|² ≪ N^{3-c+0.00011}`, what the paper derives "as usual". -/
structure InputsM where
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  C9 : ℝ
  C86 : ℝ
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < (D1c N k).re) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ (D1c N k).re)
  minorL2 : ∀ N, N0 ≤ N → ∫ α in per N \ major N, ‖H N α‖ ^ 2 ≤ C9 * (N : ℝ) ^ (3 - c + 0.00011)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `InputsM` gives `InputsC`, by `sec9_window`. -/
def InputsM.toInputsC (J : InputsM) : InputsC :=
  { D6 := J.D6, S := J.S, S_ge := J.S_ge, N0 := max J.N0 1, Cerr := J.Cerr, c1 := J.c1,
    c1_pos := J.c1_pos, C9 := J.C9, C86 := J.C86
    lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
    sec9 := fun N hN => (sec9_window (lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN))).trans
      (J.minorL2 N (le_trans (le_max_left _ _) hN))
    eq86 := fun N hN => J.eq86 N (le_trans (le_max_left _ _) hN) }

/-- CONDITIONAL ON `InputsM`: the paper's Theorem `E(x) ≪ x^{0.879}`. -/
theorem lu_of_inputsM (J : InputsM) : PowerBound 0.879 := lu_of_inputsC J.toInputsC

/-- CONDITIONAL ON `InputsM`: `E X ≪ X^{0.8789126}`. -/
theorem lu_sharp_of_inputsM (J : InputsM) : PowerBound θ := lu_sharp_of_inputsC J.toInputsC

/-- CONDITIONAL ON `InputsM`: Pintz's eventual form `E X < X^{0.879}`. -/
theorem lu_eventually_of_inputsM (J : InputsM) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputsC J.toInputsC

end LeanLab.ExceptionalSet.Lu2010Sec9

#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.F_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.H_eq_F0
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.norm_ee
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.H_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.D2c_eq_coeff
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.G_memLp
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.sec9_parseval
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.sec9_window
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.InputsM.toInputsC
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.lu_of_inputsM
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.lu_sharp_of_inputsM
#print axioms LeanLab.ExceptionalSet.Lu2010Sec9.lu_eventually_of_inputsM
