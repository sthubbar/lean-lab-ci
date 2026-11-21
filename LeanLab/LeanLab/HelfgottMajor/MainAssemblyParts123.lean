import LeanLab.HelfgottMajor.Decomp123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, 2026-11-21. P0014, Helfgott,
Major arcs for Goldbach's problem, arXiv 1305.2897v4, Theorem 1.1, page 3, proof on pages 56
and 57.

The upper part of the spine of `Decomp123.theorem_1_1`, written as twins that take the five
branch tops as arguments instead of the sealed open leaves. Each argument has the exact type of
a sealed declaration, written with `type_of%`:
- `corollary_3_2_k0`, P0014 Corollary 3.2, page 10, display 3.4
- `tail_mass_of_corollary`, P0014 Lemma 4.5, page 41, displays 4.33 to 4.35
- `lemma_4_1_gaussian_corrected`, P0014 Lemma 4.1, page 31, corrected
- `residue_main_conj_bound_of_zeros`, P0014 Lemma 4.2 and display 4.23, pages 35 to 37
- `low_zero_bound_slack`, P0014 Lemma 4.4, display 4.29, page 39
Every proof below is the sealed proof with the tainted dependency replaced by the argument.
The file has no sorry and no new definition. The branch twins that discharge the arguments
from named hypotheses are in MainAssembly123.lean.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainAssemblyParts123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- Twin of `SplitGaussian123.tail_mass_integral`, P0014 Lemma 4.5, page 41, displays 4.33
to 4.35, taking the two pieces as arguments. -/
theorem tail_mass_integral_of_parts
    (hcor : type_of% @SplitGaussian123.corollary_3_2_k0)
    (htail : type_of% @SplitGaussian123.tail_mass_of_corollary)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) :=
  htail q χ hχ δ T hT hzeros
    (fun s h0 h1 hτ => hcor δ s h0 h1 hτ)

/-- Twin of `SplitGaussian123.high_zero_bound`, P0014 displays 4.35, 4.36 and 4.41, page 42. -/
theorem high_zero_bound_of_parts
    (hcor : type_of% @SplitGaussian123.corollary_3_2_k0)
    (htail : type_of% @SplitGaussian123.tail_mass_of_corollary)
   (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖highZeros χ δ x T‖ ≤
      log (q * T / (2 * π)) *
        (4.329 * exp (-0.1598 * T) +
          0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) * x := by
  -- Route burst session 9: display 4.35 bound, then displays 4.36 and 4.41, page 42.
  obtain ⟨hs, hm⟩ := tail_mass_integral_of_parts hcor htail q χ hχ δ T hT hzeros
  apply high_zero_bound_of_mass χ δ x T _ hx hs
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have he := TailIntegral123.exp_integral_bound q T hT100
  have hg : TailIntegral123.gaussianTailIntegral q δ T ≤
      0.18787 * |δ| * log (q * T / (2 * π)) *
        exp (-0.1065 * (T / (π * |δ|)) ^ 2) := by
    by_cases hδ : δ = 0
    · simp [hδ, TailIntegral123.gaussianTailIntegral]
    · exact TailIntegral123.gaussian_integral_bound q δ T hδ hT
  have hlog : 0 ≤ log ((q : ℝ) * T / (2 * π)) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    apply log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pi_lt_four]
  calc
    _ ≤ 4.226 * (TailIntegral123.expTailIntegral q T +
          TailIntegral123.gaussianTailIntegral q δ T) := hm
    _ ≤ 4.226 * (1.0242 * log (q * T / (2 * π)) * exp (-0.1598 * T) +
        0.18787 * |δ| * log (q * T / (2 * π)) *
          exp (-0.1065 * (T / (π * |δ|)) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add he hg) (by norm_num)
    _ ≤ _ := by
      nlinarith [mul_nonneg hlog (exp_pos (-0.1598 * T)).le,
        mul_nonneg hlog (mul_nonneg (abs_nonneg δ)
          (exp_pos (-0.1065 * (T / (π * |δ|)) ^ 2)).le)]


/-- Twin of `Lemma41Corrected123.explicit_formula_remainder_corrected`, P0014 page 44, the
corrected explicit formula, taking Lemma 4.1 corrected and the residue bound as arguments. -/
theorem explicit_formula_remainder_corrected_of_parts
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected)
    (hres : type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros)
    (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ 3 * log q + 13.347 * |δ| + 16.695 + log x ∧
      ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
        lowZeros χ δ x T + highZeros χ δ x T + R‖ ≤
        (log q + 6.01) * (1 + 6 * |δ|) / sqrt x := by
  classical
  have hT100 : 100 ≤ T := (le_max_right _ _).trans hT
  have hz58 : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ 5 / 8 → s.re = 1 / 2 :=
    fun s h0 h1 h2 h3 => hzeros s h0 h1 h2 (by linarith)
  obtain ⟨c, hc, hE⟩ := h41 x hx q χ hχ δ T hT
  refine ⟨_, ?_, hE.trans ?_⟩
  · have h1 := hres χ hχ hz58
    have h2 := Lemma41Terms.c0_gauss (abs_nonneg δ)
    have h0 : 0 ≤ log x := log_nonneg hx
    have h3 : ‖(if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)‖ ≤ log x := by
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      · simpa using h0
    refine (norm_add_le _ _).trans ?_
    have h4 := norm_add_le
      (if q = 1 then ((log (2 * π) : ℝ) : ℂ) else
        ((log (2 * π / q) + Real.eulerMascheroniConstant : ℝ) : ℂ) -
          (starRingEnd ℂ) (deriv (DirichletCharacter.LFunction χ) 1 /
            DirichletCharacter.LFunction χ 1))
      (if q ≠ 1 ∧ χ.Even then ((log x : ℝ) : ℂ) else 0)
    linarith [abs_nonneg δ]
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
    have hl : 0 ≤ log (q : ℝ) + 6.01 := by linarith [log_nonneg hq1]
    have hr := Lemma41Terms.repaired (abs_nonneg δ)
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg x)
    exact mul_le_mul_of_nonneg_left hr hl


/-- Twin of `Lemma41Corrected123.gaussian_explicit_estimate_corrected`, P0014 Proposition 4.6,
pages 43 and 44, display 4.43 with the factor 6 repair. -/
theorem gaussian_explicit_estimate_corrected_of_parts
    (hcor : type_of% @SplitGaussian123.corollary_3_2_k0)
    (htail : type_of% @SplitGaussian123.tail_mass_of_corollary)
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected)
    (hres : type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros)
    (hlow : type_of% @Lemma41Corrected123.low_zero_bound_slack)
    (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    ‖Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0)‖ ≤
      (log (q * T / (2 * π)) *
          (4.329 * exp (-0.1598 * T) +
            0.802 * |δ| * exp (-0.1065 * (T / (π * |δ|)) ^ 2)) +
        (2.337 * sqrt T * log (q * T) + 21.817 * sqrt T + 2.85 * log q + 74.38) /
          sqrt x + (3 * log q + 14 * |δ| + 17) / x +
        (log q + 6) * (1 + 6 * |δ|) / (x * sqrt x)) * x :=
  Lemma41Corrected123.assembly_of_components_corrected x hx q χ δ T
    (explicit_formula_remainder_corrected_of_parts h41 hres x hx q χ hχ δ T hT hzeros)
    (hlow x hx q χ hχ δ T hT hzeros)
    (high_zero_bound_of_parts hcor htail x hx q χ hχ δ T hT hzeros)


open LeanLab.HelfgottMajor.Decomp123 in
/-- Twin of `Decomp123.gaussian_explicit_estimate`, P0014 Proposition 4.6, display 4.43. -/
theorem gaussian_explicit_estimate_of_parts
    (hcor : type_of% @SplitGaussian123.corollary_3_2_k0)
    (htail : type_of% @SplitGaussian123.tail_mass_of_corollary)
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected)
    (hres : type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros)
    (hlow : type_of% @Lemma41Corrected123.low_zero_bound_slack)
    (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    MajorShape etaHeart χ δ x (gaussianError q δ x T) := by
  -- SPLIT 2026-11-12 route burst: Lemma 4.1, Lemma 4.4 and Lemma 4.5 pieces in
  -- SplitGaussian123, combined by the proved page 43 and 44 assembly.
  -- Route burst 2026-11-15 p6: Lemma 4.1 enters in corrected form, with the log x of the
  -- double pole at s = 0 for even characters; the printed Lemma 4.1 leaf is SUSPECTED FALSE
  -- and is no longer used here. The log x is paid by two units of proved slack in the low
  -- zero bound, since log x is at most 2 sqrt x. See Lemma41Corrected123.
  unfold MajorShape gaussianError
  exact gaussian_explicit_estimate_corrected_of_parts hcor htail h41 hres hlow x hx q χ hχ δ T hT hzeros


open LeanLab.HelfgottMajor.Decomp123 in
/-- Twin of `Decomp123.theorem_1_1`, P0014 Theorem 1.1, page 3, proof on pages 56 and 57,
taking the five branch tops as arguments. -/
theorem theorem_1_1_of_parts
    (hcor : type_of% @SplitGaussian123.corollary_3_2_k0)
    (htail : type_of% @SplitGaussian123.tail_mass_of_corollary)
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected)
    (hres : type_of% @Lemma41Corrected123.residue_main_conj_bound_of_zeros)
    (hlow : type_of% @Lemma41Corrected123.low_zero_bound_slack) :
    Theorem11 := by
  intro hG x hx q _ hq χ hχ δ hδ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq' : (q : ℝ) ≤ 300000 := by exact_mod_cast hq
  have hδ' : |δ| ≤ 1200000 / (q : ℝ) := by norm_num at hδ ⊢; exact hδ
  have hx' : (1e8 : ℝ) ≤ x := by norm_num at hx ⊢; exact hx
  have hz := verified_zeros hG q hq χ hχ
  have hp := gaussian_explicit_estimate_of_parts hcor htail h41 hres hlow x (by linarith) q χ hχ δ (1e8 / q)
    (height_conditions hq1 hq' hδ').2 hz
  have hb := error_bound hq1 hq' hδ' hx'
  unfold MajorShape at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right hb (by linarith))


end LeanLab.HelfgottMajor.MainAssemblyParts123

#print axioms LeanLab.HelfgottMajor.MainAssemblyParts123.theorem_1_1_of_parts
