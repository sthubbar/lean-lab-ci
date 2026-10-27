/-
P0095 W. C. Lu 2010, the arc split (9), p. 2362. Unit U-6845, CLOUD MANUAL-M1, 2026-10-21,
track T1.

p. 2362: 𝔐 = ⋃_{1≤q≤P} ⋃_{0≤h≤q-1, (h,q)=1} [h/q - 1/(qQ), h/q + 1/(qQ)],
𝔪 = [-1/Q, 1-1/Q] \ 𝔐, and (9) D̃(k) = ∫_𝔐 + ∫_𝔪 = D₁(k) + D₂(k). Here `D1c` and `D2c` are
these integrals, taken over the period interval `(-1/Q, 1-1/Q]` intersected with 𝔐 and with
its complement; 𝔐 lies in the closed period interval for large N, so this changes the
integrals by at most a null set. (9) is then PROVED, `Dtil_split`. The real part is taken
where (84) and (85) compare D₁ with a real number; D̃ is real by `Dtil_eq_Dt`.

After this unit the Theorem is CONDITIONAL ON `InputsC`: (84) or (85), Section 9 and (86)
for these concrete D₁ and D₂, with D₆ and 𝔖 ≥ 1 still existential.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Orth

namespace LeanLab.ExceptionalSet.Lu2010Arcs
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Lemma1
  LeanLab.ExceptionalSet.Lu2010Orth

/-- The major arcs 𝔐 of p. 2362, with `P = N^c`, `Q = N^{3/4}`. -/
def major (N : ℕ) : Set ℝ :=
  ⋃ q ∈ Finset.Icc 1 ⌊PP N⌋₊, ⋃ h ∈ (Finset.range q).filter (fun h => Nat.Coprime h q),
    Set.Icc ((h : ℝ) / q - 1 / (q * QQ N)) ((h : ℝ) / q + 1 / (q * QQ N))

theorem major_measurable (N : ℕ) : MeasurableSet (major N) := by
  unfold major
  exact Finset.measurableSet_biUnion _ (fun q _ =>
    Finset.measurableSet_biUnion _ (fun h _ => measurableSet_Icc))

/-- The period interval `(-1/Q, 1-1/Q]`. -/
noncomputable def per (N : ℕ) : Set ℝ := Set.Ioc (-1 / QQ N) (1 - 1 / QQ N)

/-- The inner `t`-integral of `D̃`. -/
noncomputable def F (N k : ℕ) (α : ℝ) : ℂ :=
  ∫ t in Set.Icc (aa N) (bb N),
    Ssum (t * dd N + dd N) (t * dd N) α * Ssum (N - t * dd N) (N - t * dd N - dd N) α *
      ee (-(k * α))

/-- `D₁(k) = ∫_𝔐`. -/
noncomputable def D1c (N k : ℕ) : ℂ := ∫ α in per N ∩ major N, F N k α

/-- `D₂(k) = ∫_𝔪`, `𝔪 = [-1/Q, 1-1/Q] \ 𝔐`. -/
noncomputable def D2c (N k : ℕ) : ℂ := ∫ α in per N \ major N, F N k α

theorem F_continuous {N : ℕ} (hN : 0 < N) (k : ℕ) : Continuous (F N k) := by
  have : F N k = fun α => ∑ n ∈ range (k + 2 * N + 1), ∑ m ∈ range (k + 2 * N + 1),
      (cc N n m : ℂ) * ee (((n : ℤ) + m - k : ℤ) * α) := by
    funext α; exact inner_eq hN k α
  rw [this]
  exact continuous_finset_sum _ (fun n _ => continuous_finset_sum _ (fun (m : ℕ) _ =>
    continuous_const.mul (ee_continuous (((n : ℤ) + (m : ℤ) - k : ℤ) : ℝ))))

/-- **(9), PROVED**: `D̃(k) = D₁(k) + D₂(k)`. -/
theorem Dtil_split {N : ℕ} (hN : 0 < N) (k : ℕ) : Dtil N k = D1c N k + D2c N k := by
  have hQ : 0 < QQ N := rpow_pos_of_pos (by exact_mod_cast hN) _
  have hle : -1 / QQ N ≤ 1 - 1 / QQ N := by
    have : 0 < 1 / QQ N := by positivity
    rw [neg_div]; linarith
  unfold Dtil D1c D2c
  rw [intervalIntegral.integral_of_le hle]
  have hint : IntegrableOn (F N k) (per N) :=
    ((F_continuous hN k).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  exact (integral_inter_add_sdiff (major_measurable N) hint).symm

/-- `D̃(k)` is real. -/
theorem Dtil_im {N : ℕ} (hN : 0 < N) (k : ℕ) : (Dtil N k).im = 0 := by
  rw [Dtil_eq_Dt hN]; simp

/-- **Cited input**, Lu's (84) or (85), Section 9 and (86), for the concrete arc integrals
`D₁ = D1c`, `D₂ = D2c`; `D₆` and `𝔖` with `𝔖(k) ≥ 1` for even `k` stay existential. -/
structure InputsC where
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
  sec9 : ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D2c N k‖ ^ 2 ≤ C9 * (N : ℝ) ^ (3 - c + 0.00011)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `InputsC` gives `InputsO`, with `D₁ = Re D1c` and `D₂ = Re D2c`. -/
noncomputable def InputsC.toInputsO (J : InputsC) : InputsO :=
  { D1 := fun N k => (D1c N k).re, D2 := fun N k => ((D2c N k).re : ℂ), D6 := J.D6,
    S := J.S, S_ge := J.S_ge, N0 := max J.N0 1, Cerr := J.Cerr, c1 := J.c1,
    c1_pos := J.c1_pos, C9 := J.C9, C86 := J.C86
    eq9 := fun N hN k _ => by
      have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
      have hs := Dtil_split hNpos k
      have him := Dtil_im hNpos k
      apply Complex.ext
      · simp [hs]
      · simp only [Complex.add_im, Complex.ofReal_im, add_zero]; exact him
    lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
    sec9 := fun N hN => by
      refine le_trans ?_ (J.sec9 N (le_trans (le_max_left _ _) hN))
      apply Finset.sum_le_sum; intro k _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
    eq86 := fun N hN => J.eq86 N (le_trans (le_max_left _ _) hN) }

/-- CONDITIONAL ON `InputsC`: the paper's Theorem `E(x) ≪ x^{0.879}`. -/
theorem lu_of_inputsC (J : InputsC) : PowerBound 0.879 := lu_of_inputsO J.toInputsO

/-- CONDITIONAL ON `InputsC`: `E X ≪ X^{0.8789126}`. -/
theorem lu_sharp_of_inputsC (J : InputsC) : PowerBound θ := lu_sharp_of_inputsO J.toInputsO

/-- CONDITIONAL ON `InputsC`: Pintz's eventual form `E X < X^{0.879}`. -/
theorem lu_eventually_of_inputsC (J : InputsC) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputsO J.toInputsO

end LeanLab.ExceptionalSet.Lu2010Arcs

#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.major_measurable
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.F_continuous
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.Dtil_split
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.Dtil_im
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.InputsC.toInputsO
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.lu_of_inputsC
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.lu_sharp_of_inputsC
#print axioms LeanLab.ExceptionalSet.Lu2010Arcs.lu_eventually_of_inputsC
