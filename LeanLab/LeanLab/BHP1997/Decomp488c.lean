/-
P0069, page 22, horizontal sides for display 3.36.
The final Perron bound is CONDITIONAL on the remaining horizontal leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp488b

namespace LeanLab.BHP1997.DecompC165a.Contour230
open Classical Complex MeanValue132 MeasureTheory Set Filter
open scoped Topology

/-- LEAF. Page 22, horizontal segment estimate before display 3.36.
Subtracting the normalized rectangle integral removes the residue exactly.
The remaining difference is the two horizontal integrals at the safe height.
This is the uniform analytic input from Lemma 8. CITED and OPEN. -/
theorem safe_height_horizontal_bound (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x →
      1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖(1 / (2 * (Real.pi : ℂ) * I)) *
          ((∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
            integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
              ((σ : ℂ) - height T t * I)) -
           (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
            integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
              ((σ : ℂ) + height T t * I)))‖ ≤
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) := by
  sorry

/-- Page 22, the rectangle bookkeeping before display 3.36.
The right line minus the left line minus the rectangle is the negative horizontal part. -/
theorem horizontal_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x N T t : ℝ) :
    rightIntegral x N T χ t - lineIntegral N T χ t -
      RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((height T t : ℂ) * I))
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I) =
      -((1 / (2 * (Real.pi : ℂ) * I)) *
        ((∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
            ((σ : ℂ) - height T t * I)) -
         (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
            ((σ : ℂ) + height T t * I)))) := by
  have he (u : ℝ) : Thm4.half t + (u : ℂ) * I = Thm4.half (t + u) := by
    unfold Thm4.half
    push_cast
    ring
  have hleft : lineIntegral N T χ t =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u in (-height T t)..height T t,
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((u : ℂ) * I) := by
    simp only [lineIntegral, rawLineIntegral, integrand, he]
  rw [hleft]
  unfold rightIntegral RectangleIntegral' RectangleIntegral HIntegral VIntegral
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
    Complex.add_re, add_zero, Complex.neg_im, Complex.mul_im, zero_mul,
    zero_add, Complex.add_im, Complex.ofReal_zero, Complex.ofReal_neg, neg_mul, smul_eq_mul, sub_eq_add_neg]
  have hcoef : ((1 / (2 * Real.pi) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ) * I)) * I := by
    push_cast
    field_simp
  rw [hcoef]
  ring

/-- Page 22, the absolutely convergent part of either horizontal segment.
Stay delta to the right of real part one for the L-function.
No convexity or other cited input is used. -/
theorem right_half_horizontal_integrand_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b t : ℝ) {σ u δ : ℝ}
    (hδ : 0 < δ) (hσ : 1 / 2 + δ ≤ σ) (hu : u ≠ 0) :
    ‖integrand a b χ t ((σ : ℂ) + u * I)‖ ≤
      (1 + 1 / δ) *
        ((Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u|) := by
  have hδ' : 0 < σ - 1 / 2 := by linarith
  have he : Thm4.half t + ((σ : ℂ) + u * I) =
      (((1 + (σ - 1 / 2) : ℝ) : ℂ) + (t + u) * I) := by
    unfold Thm4.half
    push_cast
    ring
  have hL : ‖χ.LFunction (Thm4.half t + ((σ : ℂ) + u * I))‖ ≤ 1 + 1 / δ := by
    rw [he]
    have hi : 1 / (σ - 1 / 2) ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ (by linarith)
    have hh := LFunction_right_bound χ (t := t + u) hδ'
    push_cast at hh ⊢
    linarith
  have hn : |u| ≤ ‖((σ : ℂ) + u * I)‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + u * I)
  have hz : ((σ : ℂ) + u * I) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr hu).trans_le hn)
  have hk := kernel_strip_bound a b hz
  have hk' : ‖kernel a b ((σ : ℂ) + u * I)‖ ≤
      (Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u| := by
    apply hk.trans
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hu) hn
  exact (norm_mul _ _).le.trans (mul_le_mul hL hk' (norm_nonneg _) (by positivity))

/-- Page 22, the strip estimate supplied directly by the cited Lemma 8.
This keeps the epsilon loss explicit. CONDITIONAL on Lemma8. -/
theorem strip_horizontal_integrand_bound (h8 : MeanValue132.Lemma8) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ a b t σ u : ℝ,
      0 ≤ σ → σ ≤ 1 / 2 → u ≠ 0 → 1 / 4 ≤ |t + u| →
        ‖integrand a b χ t ((σ : ℂ) + u * I)‖ ≤
          C * (((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4) *
            ((Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u|) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h8 ε hε
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ a b t σ u hσ0 hσ1 hu hsep
  let s : ℂ := (((1 / 2 + σ : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)
  have hp : 1 / 4 ≤ ‖s - 1‖ := by
    apply hsep.trans
    simpa [s] using Complex.abs_im_le_norm (s - 1)
  have hs : s ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero] at hp
    norm_num at hp
  have hpole : 1 / ‖s - 1‖ ≤ 4 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hp
    norm_num at hh
    simpa only [one_div] using hh
  have hh := hbound q hq χ (1 / 2 + σ) (t + u) (by linarith) (by linarith) hs
  have hexp : 1 + ε - (1 / 2 + σ) = 1 / 2 + ε - σ := by ring
  rw [hexp] at hh
  have he : Thm4.half t + ((σ : ℂ) + u * I) = s := by
    dsimp [s, Thm4.half]
    push_cast
    ring
  have hL : ‖χ.LFunction (Thm4.half t + ((σ : ℂ) + u * I))‖ ≤
      C * (((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4) := by
    rw [he]
    have ht : ((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 1 / ‖s - 1‖ ≤
        ((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4 := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left ht hC.le)
  have hn : |u| ≤ ‖((σ : ℂ) + u * I)‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + u * I)
  have hz : ((σ : ℂ) + u * I) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr hu).trans_le hn)
  have hk := kernel_strip_bound a b hz
  have hk' : ‖kernel a b ((σ : ℂ) + u * I)‖ ≤
      (Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u| := by
    apply hk.trans
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hu) hn
  exact (norm_mul _ _).le.trans (mul_le_mul hL hk' (norm_nonneg _) (by positivity))


/-- Page 22, display 3.36. The residue identity bounds the rectangle contribution. -/
theorem safe_rectangle_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x N T : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hT : 2 ≤ T) (t : ℝ) :
    ‖RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
      (-((height T t : ℂ) * I))
      (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)‖ ≤
        12 * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  let c : ℝ := 1 / 2 + 1 / Real.log x
  let H : ℝ := height T t
  have hH : 1 ≤ H := (height_spec (t := t) hT).2.1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 1 / 2 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hre : (-((H : ℂ) * I)).re ≤ ((c : ℂ) + H * I).re := by
    simp; linarith
  have him : (-((H : ℂ) * I)).im ≤ ((c : ℂ) + H * I).im := by
    simp; linarith
  by_cases hχ : χ = 1
  · subst χ
    simp only [ite_true]
    by_cases ht : |t| < H
    · have hp : Rectangle (-((H : ℂ) * I)) ((c : ℂ) + H * I) ∈
          𝓝 (1 - Thm4.half t) := by
        rw [rectangle_mem_nhds_iff]
        have htt := abs_lt.mp ht
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
          sub_self, neg_zero, Complex.add_re, add_zero, Complex.neg_im,
          Complex.mul_im, zero_mul, zero_add, Complex.add_im, Complex.sub_re,
          Complex.one_re, Complex.sub_im, Complex.one_im, Thm4.half]
        rw [Set.uIoo_of_le (by linarith : (0 : ℝ) ≤ c),
          Set.uIoo_of_le (by linarith : -H ≤ H)]
        constructor <;> constructor <;> norm_num at * <;> linarith
      rw [principal_rectangle _ _ _ hre him hp]
      convert half_endpoint_residue_bound q hN t using 1 <;> ring
    · have hne : |t| ≠ H := by
        intro he
        rcases (abs_eq (by linarith : 0 ≤ H)).mp he with he | he
        · have hh := (height_spec (t := t) hT).2.2.2.1
          change 1 / 4 ≤ |t - H| at hh
          rw [he, sub_self, abs_zero] at hh
          norm_num at hh
        · have hh := (height_spec (t := t) hT).2.2.2.2
          change 1 / 4 ≤ |t + H| at hh
          rw [he, neg_add_cancel, abs_zero] at hh
          norm_num at hh
      have hp : 1 - Thm4.half t ∉
          Rectangle (-((H : ℂ) * I)) ((c : ℂ) + H * I) := by
        intro hp
        have hh := hp.2
        change (1 - Thm4.half t).im ∈
          Set.uIcc (-((H : ℂ) * I)).im ((c : ℂ) + H * I).im at hh
        simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
          add_zero, Complex.add_im, zero_add, Complex.sub_im, Complex.one_im] at hh
        have hh' : -t ∈ Set.uIcc (-H) H := by simpa [Thm4.half] using hh
        rw [Set.uIcc_of_le (by linarith : -H ≤ H)] at hh'
        have habs : |t| ≤ H := abs_le.mpr ⟨by linarith [hh'.2], by linarith [hh'.1]⟩
        exact hne (le_antisymm habs (le_of_not_gt ht))
      rw [principal_rectangle_outside _ _ _ hp, norm_zero]
      positivity
  · have hd := nonprincipal_integrand_entire ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) t χ hχ
    have hh : RectangleIntegral
        (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((H : ℂ) * I)) ((c : ℂ) + H * I) = 0 :=
      HolomorphicOn.vanishesOnRectangle hd.differentiableOn subset_rfl
    simp only [hχ, ite_false, mul_zero]
    change ‖RectangleIntegral' _ (-((H : ℂ) * I)) ((c : ℂ) + H * I)‖ ≤ 0
    rw [RectangleIntegral', hh, smul_zero, norm_zero]

/-- Page 22, display 3.36. Assembly from the three smaller Perron pieces.
The rectangle contribution uses the proved principal residue identity.
CONDITIONAL on safe_height_horizontal_bound. -/
theorem regularized_perron_assembly (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖partialSum N χ t‖ ≤ ‖lineIntegral N T χ t‖ +
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) +
          C * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  obtain ⟨A, hA, hrem⟩ := summed_perron_remainders
  obtain ⟨B, hB, hhor⟩ := safe_height_horizontal_bound h8
  refine ⟨A + B + 12, by positivity, ?_⟩
  intro x N T q _ χ t hx hN hNx hT hTx hq hqx ht
  have hr := hrem x N T q χ t hx hN hNx hT hTx
  rw [← rightIntegral_eq_perronSeries χ hx N T t] at hr
  have hh := hhor x N T q χ t hx hN hNx hT hTx hq hqx ht
  have hh' : ‖rightIntegral x N T χ t - lineIntegral N T χ t -
      RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((height T t : ℂ) * I))
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)‖ ≤
      B * Real.log x * (Real.sqrt q / Real.sqrt T) +
      B * Real.log x * (Real.sqrt N / T) := by
    rw [horizontal_identity, norm_neg]
    exact hh
  have hres := safe_rectangle_bound χ hx hN hT t
  let P := partialSum N χ t
  let Q := rightIntegral x N T χ t
  let J := lineIntegral N T χ t
  let R := RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
    (-((height T t : ℂ) * I))
    (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)
  have hPQ := norm_sub_le_norm_sub_add_norm_sub P Q J
  have hQR := norm_sub_le_norm_sub_add_norm_sub (Q - J) R 0
  have hPJ := norm_sub_le_norm_sub_add_norm_sub P J 0
  simp only [sub_zero] at hQR hPJ
  have hl : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  have hz : 0 ≤ (if χ = 1 then Real.sqrt N / (1 + |t|) else 0 : ℝ) := by
    split_ifs <;> positivity
  have hq0 : 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) := by positivity
  have hN0 : 0 ≤ Real.log x * (Real.sqrt N / T) := by positivity
  change ‖P - Q‖ ≤ _ at hr
  change ‖Q - J - R‖ ≤ _ at hh'
  change ‖R‖ ≤ _ at hres
  change ‖P‖ ≤ ‖J‖ + _ + _ + _
  have hm1 := mul_nonneg hA.le hq0
  have hm2 := mul_nonneg hA.le hz
  have hm3 := mul_nonneg hB.le hz
  nlinarith

end LeanLab.BHP1997.DecompC165a.Contour230
