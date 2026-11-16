/-
P0069 page 11 displays 3.3 and 3.4 and the citations on page 12.
The two existing cited leaves move here with their sealed statements unchanged.
The mean square estimate uses Gallagher smoothing and the proved sampling step.
The large value estimate remains OPEN. Their constants are uniform in F.
The elementary finite Halasz and subdivision steps already exist in Decomp492b.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165
import LeanLab.BHP1997.Decomp513b
import LeanLab.BHP1997.HybridWindow605
import LeanLab.BHP1997.CriticalLine605

namespace LeanLab.BHP1997.Decomp513a
open Finset MeasureTheory MeanSquareC165
open LeanLab.BHP1997.Gallagher605

/-- P0069 page 11 display 3.3, the continuous critical line input.
Gallagher1970 page 331 display 13 applies to coefficients a n divided by sqrt n. -/
theorem dirPoly_integral_square_sum (a : ℕ → ℂ) {c1 c2 F T : ℝ}
    {q : ℕ} [NeZero q] (hlo : 0 < c1 * F) (hT : 1 ≤ T) :
    (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..T, ‖Thm4.dirPoly a c1 c2 F χ (Thm4.half t)‖ ^ 2) ≤
      (2 * Real.pi ^ 3) * ((q : ℝ) * T + c2 * F) * energy a c1 c2 F := by
  classical
  let N := ⌊c2 * F⌋₊
  let S := (Finset.range (N + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  let b (n : ℕ) : ℂ := if n ∈ S then a n / (n : ℂ) ^ (1 / 2 : ℂ) else 0
  have hnpos (n : ℕ) (hn : n ∈ S) : 0 < (n : ℝ) :=
    hlo.trans (mem_filter.mp hn).2.1
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro n hn
    have hn0 : 0 < n := by exact_mod_cast hnpos n hn
    exact mem_Icc.mpr ⟨by omega, by
      have := mem_range.mp (mem_filter.mp hn).1
      omega⟩
  have hpoly (χ : DirichletCharacter ℂ q) (t : ℝ) :
      characterPolynomial χ b N t = Thm4.dirPoly a c1 c2 F χ (Thm4.half t) := by
    unfold characterPolynomial Thm4.dirPoly
    change (∑ n ∈ Finset.Icc 1 N, b n * χ n *
      Complex.exp (-((Real.log n * t : ℝ) : ℂ) * Complex.I)) =
      ∑ n ∈ S, a n * χ n / (n : ℂ) ^ Thm4.half t
    rw [← Finset.sum_subset hsub (by
      intro n hn hnS
      simp [b, hnS])]
    apply sum_congr rfl
    intro n hn
    dsimp only [b]
    rw [if_pos hn]
    exact critical_line_term n (hnpos n hn) (a n) (χ n) t
  have hbn (n : ℕ) (hn : n ∈ S) : ‖b n‖ ^ 2 = ‖a n‖ ^ 2 / (n : ℝ) := by
    simp only [b, if_pos hn]
    exact critical_line_coefficient_norm_sq n (hnpos n hn) (a n)
  have henergy : (∑ n ∈ Finset.Icc 1 N,
      ((q : ℝ) * T + n) * ‖b n‖ ^ 2) ≤
      ((q : ℝ) * T + c2 * F) * energy a c1 c2 F := by
    rw [← Finset.sum_subset hsub (by intro n hn hnS; simp [b, hnS])]
    change _ ≤ ((q : ℝ) * T + c2 * F) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ)
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    rw [hbn n hn]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    linarith [(mem_filter.mp hn).2.2]
  have h := fixed_modulus_hybrid_mean_value q N b hT
  simp_rw [hpoly] at h
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergy
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 3))

end LeanLab.BHP1997.Decomp513a

namespace LeanLab.BHP1997.DecompC165c
open MeanSquareC165

/-- P0069 page 11 Lemma 1 display 3.3 and the source citation on page 12.
Gallagher1970 page 331 Theorem 2 display 13 gives the continuous square estimate.
Montgomery1971 page 3 Lemma 1.4 display 1.7 supplies the sampling route.
The proof below keeps the sealed statement and a constant uniform in F. -/
theorem hybrid_mean_square : Lemma1MeanSquare := by
  intro B c1 c2 hc1 hc2
  classical
  have hc2pos : 0 < c2 := hc1.trans hc2
  let K : ℝ := 2 * Real.pi ^ 3
  let D : ℝ := 1 + |Real.log c2| / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K * (2 + c2) * (1 / Real.log 2 + 2 * D), by positivity, ?_⟩
  intro x F T q S a ha hx hF hFx hT hTx hq hqx hspace htimes
  letI : NeZero q := ⟨by omega⟩
  have hFpos : 0 < F := by linarith
  have hlo : 0 < c1 * F := mul_pos hc1 hFpos
  have hTpos : 0 < T := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  let L : ℝ := D * Real.log x
  have hL : 0 < L := mul_pos hD hlogx
  let H : ℝ := K * ((q : ℝ) * (T + 1) + c2 * F)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hE : 0 ≤ energy a c1 c2 F := by
    unfold energy
    exact Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hmoment (b : ℕ → ℂ) :
      (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..(T + 1),
        ‖Thm4.dirPoly b c1 c2 F χ (Thm4.half t)‖ ^ 2) ≤
        H * energy b c1 c2 F := by
    apply le_trans _ (Decomp513a.dirPoly_integral_square_sum (q := q) b hlo (by linarith : 1 ≤ T + 1))
    apply Finset.sum_le_sum
    intro χ hχ
    have hc := (Decomp513b.dirPoly_contDiff b c1 c2 F χ hlo).continuous.norm.pow 2
    apply intervalIntegral.integral_mono_interval
      (by linarith : -(T + 1) ≤ -T) (by linarith : -T ≤ T + 1) le_rfl
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) (hc.intervalIntegrable _ _)
  let f (χ : DirichletCharacter ℂ q) (t : ℝ) := Thm4.dirPoly a c1 c2 F χ (Thm4.half t)
  let g (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    -Complex.I * Thm4.dirPoly (fun n => (Real.log n : ℂ) * a n) c1 c2 F χ (Thm4.half t)
  have hf (χ : DirichletCharacter ℂ q) (t : ℝ) : HasDerivAt (f χ) (g χ t) t :=
    Decomp513b.dirPoly_hasDerivAt a c1 c2 F χ hlo t
  have hg (χ : DirichletCharacter ℂ q) : Continuous (g χ) := by
    exact continuous_const.mul
      (Decomp513b.dirPoly_contDiff (fun n => (Real.log n : ℂ) * a n) c1 c2 F χ hlo).continuous
  have hs := Decomp513a.character_square_sampling_scaled S f g hf hg hspace hTpos.le hL htimes
  have hA : (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..(T + 1), ‖f χ t‖ ^ 2) ≤ H * energy a c1 c2 F := hmoment a
  have hB : (∑ χ : DirichletCharacter ℂ q,
      ∫ t in (-T)..(T + 1), ‖g χ t‖ ^ 2) ≤ H * (L ^ 2 * energy a c1 c2 F) := by
    simp only [g, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact (hmoment (fun n => (Real.log n : ℂ) * a n)).trans
      (mul_le_mul_of_nonneg_left (Decomp513b.log_weight_energy_le a hlo hc2pos hF hFx) hH)
  have htotal : (∑ p ∈ S, ‖f p.2 p.1‖ ^ 2) ≤ (1 + 2 * L) * H * energy a c1 c2 F := by
    apply hs.trans
    calc
      _ ≤ (1 + L) * (H * energy a c1 c2 F) + L⁻¹ * (H * (L ^ 2 * energy a c1 c2 F)) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hL.le))
      _ = _ := by field_simp [hL.ne']; ring
  have hlogfactor : 1 + 2 * L ≤ (1 / Real.log 2 + 2 * D) * Real.log x := by
    have h1 : 1 ≤ Real.log x / Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlogle)
    calc
      _ ≤ Real.log x / Real.log 2 + 2 * L := by linarith only [h1]
      _ = _ := by dsimp [L]; ring
  have hqT : 0 ≤ (q : ℝ) * T := by positivity
  have hbracket : (q : ℝ) * (T + 1) + c2 * F ≤ (2 + c2) * ((q : ℝ) * T + F) := by
    have hqt : (q : ℝ) ≤ (q : ℝ) * T := by
      simpa using mul_le_mul_of_nonneg_left (show 1 ≤ T by linarith) (Nat.cast_nonneg q)
    nlinarith [mul_nonneg hc2pos.le hqT]
  have hHbound : H ≤ K * (2 + c2) * ((q : ℝ) * T + F) := by
    dsimp [H]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbracket hK.le
  apply htotal.trans
  calc
    _ ≤ ((1 / Real.log 2 + 2 * D) * Real.log x) *
        (K * (2 + c2) * ((q : ℝ) * T + F)) * energy a c1 c2 F := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hlogfactor hHbound hH (by positivity)) hE
    _ = _ := by ring

/-- LEAF, CITED. Page 11, Lemma 1, display 3.4. Page 12 cites Montgomery reference 21,
Theorem 8.3, then Huxley reference 14, Section 2, cited not proved in the lab. U-1609 decision: a
citation wall, as for display 3.3. The weak Chebyshev consequence of 3.3 is insufficient.
`0 < V` is required: `Audit1609.large_values_zero_V_false` refutes the form with `0 ≤ V`. -/
theorem hybrid_large_values : Lemma1LargeValues := by
  sorry

end LeanLab.BHP1997.DecompC165c

