import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_real_exceptional_conductor481
import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_real_zero_bound481
import LeanLab.LanguascoPintzZaccagnini2007.SPLIT_davenport_classification481

/-!
The real character conductor conclusion of P0045 pages 5 and 6.
Supply the proved real zero theorem to the repaired conductor split.
Then use the proved primitive conductor classification for the odd radical.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

/-- P0045 page 5, conductor estimate before Lemma 4.1.
The exact real conductor conclusion with the real zero input discharged. -/
theorem real_exceptional_conductor_proved484 (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (z.1 : ℝ) :=
  real_exceptional_conductor481_split real_zero_bound481_split H T hH hT

/-- P0045 page 6, first proof paragraph of Corollary 4.2 and display 10.
Every real primitive exceptional character has odd radical at least a positive multiple of L squared. -/
theorem real_exceptional_radical_proved484 (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        (∀ a, (z.2.1 a).im = 0) → c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨c, hc, X₀, hbound⟩ := real_exceptional_conductor_proved484 H T hH hT
  refine ⟨c / 8, by positivity, X₀, ?_⟩
  intro X hX P hP z hz hreal
  have hclass := davenport_classification481_split z.1 hz.1 z.2.1 hz.2.2.1 hreal
  have h := real_radical_transfer481 hclass (hbound X hX P hP z hz hreal)
  simpa [div_mul_eq_mul_div] using h

/-- P0045 page 5, display 8 and the separation of the zeta pole before Lemma 4.1.
At fixed strip width and height the primitive principal character contributes no box zero
for all sufficiently large X, uniformly in the major arc parameter. -/
theorem principal_zeroBox_eventually_absent484 (H T : ℝ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      ∀ z ∈ zeroBox481 X H T P, z.2.1 ≠ 1 := by
  obtain ⟨σ, hσ, hbox⟩ := ZetaNoZerosInBox T
  have hgap : 0 < 1 - σ := sub_pos.mpr hσ
  have hlim : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Filter.eventually_ge_atTop (H / (1 - σ))))
  refine ⟨max X₀ 2, ?_⟩
  intro X hX P z hz hχ
  rcases z with ⟨r, χ, ρ⟩
  change χ = 1 at hχ
  obtain ⟨hr, _, hprim, hzero, hlo, _, him⟩ := hz
  change 1 ≤ r at hr
  have hr0 : r ≠ 0 := by omega
  letI : NeZero r := ⟨hr0⟩
  have hrone : r = 1 := by
    rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
    exact hprim.symm
  subst r
  have hζ : riemannZeta ρ = 0 := by
    simpa [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq] using hzero
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < X by omega))
  have hcut := hX₀ X ((le_max_left _ _).trans hX)
  have hprod : H ≤ Real.log (X : ℝ) * (1 - σ) := (div_le_iff₀ hgap).mp hcut
  have hdiv : H / Real.log (X : ℝ) ≤ 1 - σ :=
    (div_le_iff₀ hlog).mpr (by simpa [mul_comm] using hprod)
  exact hbox ρ.im him ρ.re (by linarith)
    (by simpa only [Complex.re_add_im] using hζ)

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.real_exceptional_conductor_proved484
#print axioms LeanLab.LPZ2007.real_exceptional_radical_proved484

#print axioms LeanLab.LPZ2007.principal_zeroBox_eventually_absent484
