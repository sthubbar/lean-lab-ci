import LeanLab.LPZ2007.RealZeroProof
import LeanLab.LPZ2007.Iwaniec106
import LeanLab.LPZ2007.RealConductor373

/-!
Corollary 4.2 on page 6 of P0045.
The final assembly has the exact lab type Cor42.
The analytic leaves remain conditional on the sources named below.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.Decomp106

open scoped BigOperators
open Real

/-- LEAF. P0045 page 6, first proof paragraph after display 10.
Davenport Chapter 5 supplies the conductor classification.
This leaf transfers a conductor lower bound to its odd radical. -/
theorem real_radical_transfer (hclass : RealPrimitiveModulus)
    {r : ℕ} (hr : 1 ≤ r) (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0)
    {Y : ℝ} (hY : Y ≤ r) : Y / 8 ≤ oddRad r := by
  have hnonneg : (0 : ℝ) ≤ oddRad r := Nat.cast_nonneg _
  rcases hclass r hr χ hprim hreal with h | h | h
  · have hh : (r : ℝ) = oddRad r := by exact_mod_cast h
    linarith
  · have hh : (r : ℝ) = 4 * oddRad r := by exact_mod_cast h
    linarith
  · have hh : (r : ℝ) = 8 * oddRad r := by exact_mod_cast h
    linarith

/-- LEAF. P0045 pages 5 and 6, real exceptional character case.
The real zero bound is Pintz 1976 and Goldfeld and Schinzel 1975.
Nonreal zeros of real characters use the classical zero free region proved in PNTPort.
The proof below supplies the bounded height comparison and primitive principal case. -/
theorem real_exceptional_conductor (hzero : RealZeroBound)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∀ a, (z.2.1 a).im = 0) →
        c * Lg X ^ 2 ≤ (z.1 : ℝ) := by
  obtain ⟨a, ha, hrealzero⟩ := hzero
  obtain ⟨b, b', hb, hb', hregion⟩ := LeanLab.PNTPort.DirichletZF.zero_free_region_real
  obtain ⟨σ, hσ, hzeta⟩ := ZetaNoZerosInBox T
  have hHpos : 0 < H := by linarith
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.1
    ((RealConductor373.logarithmic_majorant T).bound (by positivity : (0 : ℝ) < b / (2 * H)))
  let d := min 1 ((a / H) ^ 2)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  let V := max 1 (max U (2 * H / (1 - σ)))
  refine ⟨d * (log 2) ^ 2, exp V, by positivity, ?_⟩
  intro X P hX _ ⟨r, χ, ρ⟩ hz hreal
  have hXp : 0 < X := (exp_pos V).trans_le hX
  have hVX : V ≤ log X := by
    simpa only [log_exp] using log_le_log (exp_pos V) hX
  have hu : 1 ≤ log X := (le_max_left _ _).trans hVX
  have hu0 : 0 < log X := by linarith
  have hUX : U ≤ log X := (le_max_left _ _).trans ((le_max_right _ _).trans hVX)
  have hσX : 2 * H / (1 - σ) ≤ log X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hVX)
  have hσstrip : σ ≤ 1 - H / log X := by
    have hmul := (div_le_iff₀ (by linarith : 0 < 1 - σ)).1 hσX
    have hdiv := (div_le_iff₀ hu0).2 (show H ≤ (1 - σ) * log X by nlinarith)
    linarith
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hz.1
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  have hzL : DirichletCharacter.LFunction χ ρ = 0 := by
    simpa [Lfun, Nat.ne_of_gt hr] using hz.2.2.2.1
  have hχ : χ ≠ 1 := by
    intro he
    have hmod : r = 1 := by
      have hp := hz.2.2.1
      rw [DirichletCharacter.isPrimitive_def, he, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    have hzζ : riemannZeta ρ = 0 := by
      subst r
      simpa [he, DirichletCharacter.LFunction_modOne_eq] using hzL
    have hn := hzeta ρ.im hz.2.2.2.2.2 ρ.re
      (hσstrip.trans hz.2.2.2.2.1)
    have heq : (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I = ρ :=
      Complex.re_add_im ρ
    rw [heq] at hn
    exact hn hzζ
  have hβ : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (le_of_not_gt h) hzL
  have hident : (log 2) ^ 2 * Lg X ^ 2 = (log X) ^ 2 := by
    unfold Lg
    rw [logb]
    field_simp
  rw [mul_assoc, hident]
  by_contra hsmall
  have hrsmall : (r : ℝ) ≤ (log X) ^ 2 := by
    have hd1 : d ≤ 1 := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hd1 (sq_nonneg (log X))
    linarith
  rcases (hregion r χ hχ).1 ρ hzL with hclassic | hex
  · have hBt := RealConductor373.log_Bt_le hr hu0 hT hz.2.2.2.2.2 hrsmall
    have hs := hU (log X) hUX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0] at hs
    have hupper : log (LeanLab.PNTPort.DirichletZF.Bt r ρ.im) ≤ b / (2 * H) * log X :=
      hBt.trans ((le_abs_self _).trans hs)
    have hlogBt : 0 < log (LeanLab.PNTPort.DirichletZF.Bt r ρ.im) := by
      linarith [LeanLab.PNTPort.DirichletZF.one_le_log_Bt (N := r) ρ.im]
    have hlow : b / log (LeanLab.PNTPort.DirichletZF.Bt r ρ.im) ≤ H / log X := by
      linarith [hz.2.2.2.2.1]
    have hprod := (div_le_div_iff₀ hlogBt hu0).1 hlow
    have hmul := mul_le_mul_of_nonneg_left hupper hHpos.le
    have hid : H * (b / (2 * H) * log X) = b * log X / 2 := by field_simp
    rw [hid] at hmul
    nlinarith
  · have hρ : ρ = (ρ.re : ℂ) := by
      apply Complex.ext <;> simp [hex.2.2.2]
    have hzero' : Lfun χ (1 - ((1 - ρ.re : ℝ) : ℂ)) = 0 := by
      have he : (1 - ((1 - ρ.re : ℝ) : ℂ)) = (ρ.re : ℂ) := by push_cast; ring
      rw [he, ← hρ]
      exact hz.2.2.2.1
    have hlower := hrealzero r hz.1 χ hreal (1 - ρ.re) (by linarith) hzero'
    have hbound := RealConductor373.modulus_bound hr ha hHpos hu0 hlower
      (show 1 - ρ.re ≤ H / log X by linarith [hz.2.2.2.2.1])
    have hd2 : d ≤ (a / H) ^ 2 := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (log X))
    linarith

/-- LEAF. P0045 page 6, second proof paragraph after display 10.
Iwaniec 1974 supplies the quoted zero free region.
Its asymptotic consequence is weaker here than the printed exponential
lower bound and is exactly the quadratic bound needed by Cor42. -/
theorem nonreal_exceptional_radical (hiw : IwaniecZeroFree)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, (∃ a, (z.2.1 a).im ≠ 0) →
        c * Lg X ^ 2 ≤ (oddRad z.1 : ℝ) := by
  exact Iwaniec106.nonreal_radical_growth hiw H T hH hT

/-- LEAF. P0045 pages 5 and 6, Lemma 4.1 to Corollary 4.2.
Pintz 2006 Theorem 10 and Jutila 1977 are the outside sources.
This leaf records the explicit formula estimate before the separate
odd radical argument. Every selected modulus comes from an actual zero.
Gamma373 proves the uniform Gamma quotient estimate.
The indexed multiplicity bound and uniform choices of H and T remain open. -/
theorem explicit_formula_family (hexp : Lemma41) (hcount : JutilaBound) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 →
      ∃ (Cstar C1 : ℕ) (B H T X0 : ℝ), 1 ≤ Cstar ∧ 1 ≤ H ∧ 1 ≤ T ∧
        ∀ X : ℝ, X0 ≤ X → ∃ P : ℝ, PRange X P ∧
          ∃ rs : Finset ℕ, rs.card ≤ C1 ∧
            (∀ r ∈ rs, ∃ z ∈ EZero X H T P, z.1 = r) ∧
            (∀ n : ℕ, Even n → InJ X n → (∀ r ∈ rs, ¬ r ∣ Cstar * n) →
              ‖RM X P n - n * sing n‖ ≤ η * n * sing n) ∧
            (∀ n : ℕ, Even n → InJ X n → ‖RM X P n‖ ≤ B * n * sing n) := by
  sorry

/-- Assembly of the two character cases in the proof of display 10. -/
theorem exceptional_radical (hclass : RealPrimitiveModulus)
    (hzero : RealZeroBound) (hiw : IwaniecZeroFree)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c X0 : ℝ, 0 < c ∧ ∀ X P : ℝ, X0 ≤ X → PRange X P →
      ∀ z ∈ EZero X H T P, c * Lg X ^ 2 ≤ (oddRad z.1 : ℝ) := by
  classical
  obtain ⟨cr, Xr, hcr, hr⟩ := real_exceptional_conductor hzero H T hH hT
  obtain ⟨cn, Xn, hcn, hn⟩ := nonreal_exceptional_radical hiw H T hH hT
  refine ⟨min (cr / 8) cn, max Xr Xn, lt_min (by positivity) hcn, ?_⟩
  intro X P hX hP z hz
  by_cases hreal : ∀ a, (z.2.1 a).im = 0
  · have hc := hr X P (le_trans (le_max_left _ _) hX) hP z hz hreal
    have ht := real_radical_transfer hclass hz.1 z.2.1 hz.2.2.1 hreal hc
    have hm := mul_le_mul_of_nonneg_right (min_le_left (cr / 8) cn) (sq_nonneg (Lg X))
    calc
      min (cr / 8) cn * Lg X ^ 2 ≤ cr / 8 * Lg X ^ 2 := hm
      _ = (cr * Lg X ^ 2) / 8 := by ring
      _ ≤ (oddRad z.1 : ℝ) := ht
  · have hex : ∃ a, (z.2.1 a).im ≠ 0 := by simpa only [not_forall] using hreal
    exact le_trans
      (mul_le_mul_of_nonneg_right (min_le_right (cr / 8) cn) (sq_nonneg (Lg X)))
      (hn X P (le_trans (le_max_right _ _) hX) hP z hz hex)

/-- The exact cited lab Prop assembled from the proof leaves.
This theorem is CONDITIONAL on the unproved leaves and cited inputs. -/
theorem cor42_decomposed : Cor42 := by
  obtain ⟨η0, hη0, hf⟩ := explicit_formula_family lemma41 jutila
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηsmall
  obtain ⟨Cstar, C1, B, H, T, Xf, hC, hH, hT, hf⟩ := hf η hη hηsmall
  obtain ⟨c, Xr, hc, hr⟩ := exceptional_radical realPrimitiveModulus realZeroBound iwaniec H T hH hT
  refine ⟨Cstar, C1, c, B, max Xf Xr, hC, hc, ?_⟩
  intro X hX
  obtain ⟨P, hP, rs, hcard, hsource, hgood, hall⟩ :=
    hf X (le_trans (le_max_left _ _) hX)
  refine ⟨P, hP, rs, hcard, ?_, hgood, hall⟩
  intro r hmem
  obtain ⟨z, hz, hzr⟩ := hsource r hmem
  simpa only [hzr] using hr X P (le_trans (le_max_right _ _) hX) hP z hz

end LeanLab.LPZ2007.Decomp106

#print axioms LeanLab.LPZ2007.Decomp106.real_radical_transfer
#print axioms LeanLab.LPZ2007.Decomp106.exceptional_radical
#print axioms LeanLab.LPZ2007.Decomp106.cor42_decomposed
#print axioms LeanLab.LPZ2007.Decomp106.real_exceptional_conductor
#print axioms LeanLab.LPZ2007.Decomp106.nonreal_exceptional_radical
#print axioms LeanLab.LPZ2007.Decomp106.explicit_formula_family
