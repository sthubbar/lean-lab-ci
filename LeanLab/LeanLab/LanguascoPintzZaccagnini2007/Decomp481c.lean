import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
The reduction of the explicit formula on P0045 pages 5 and 6.
The odd radical argument is kept separate from the analytic family selection.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real
open scoped Classical

noncomputable section

/-- LEAF. P0045 page 5, multiplicity sentence before Lemma 4.1.
Group an indexed zero family by its actual character and zero value.
The occurrence bound controls its length by the sum of analytic multiplicities. -/
theorem indexed_zero_count481 {K : ℕ}
    (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
    (hmult : ∀ w, (univ.filter (fun i => z i = w)).card ≤
      analyticOrderNatAt (Lfun481 w.2.1) w.2.2) :
    (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ) := by
  exact_mod_cast (show K ≤ ∑ w ∈ univ.image z, analyticOrderNatAt (Lfun481 w.2.1) w.2.2 from by
    simpa only [← card_eq_sum_card_image z univ, card_univ, Fintype.card_fin] using
      (sum_le_sum fun w (_ : w ∈ univ.image z) => hmult w))

/-- LEAF. OPEN. P0045 page 5, Gamma pair in Lemma 4.1.
The beta integral bounds the Gamma quotient by pi in this strip.
The power of positive n is then bounded by n. This is a derived summand estimate. -/
theorem gamma_pair_bound481 {s t : ℂ}
    (hs0 : (1 / 2 : ℝ) ≤ s.re) (ht0 : (1 / 2 : ℝ) ≤ t.re)
    (hs1 : s.re ≤ 1) (ht1 : t.re ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖gammaPair481 s t n‖ ≤ Real.pi * n := by
  sorry

/-- LEAF. OPEN. P0045 page 6, paragraph before Corollary 4.2 and display 9.
Choose H and T large, then epsilon small. Separate the pole pair in Lemma 4.1,
bound the other Gamma pairs and absorb the remainder using n in J and Sing n bounded below.
Jutila controls the indexed family with multiplicity. This leaf does not assert display 10. -/
theorem explicit_formula_reduction481
    (hexp : Lemma41Statement481) (hdensity : JutilaStatement481)
    (hcount : ∀ {K : ℕ} (z : Fin K → Σ r : ℕ, DirichletCharacter ℂ r × ℂ),
      (∀ w, (univ.filter (fun i => z i = w)).card ≤
        analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
      (K : ℝ) ≤ ∑ w ∈ univ.image z, (analyticOrderNatAt (Lfun481 w.2.1) w.2.2 : ℝ))
    (hgamma : ∀ {s t : ℂ}, (1 / 2 : ℝ) ≤ s.re → (1 / 2 : ℝ) ≤ t.re →
      s.re ≤ 1 → t.re ≤ 1 → ∀ {n : ℕ}, 1 ≤ n →
        ‖gammaPair481 s t n‖ ≤ Real.pi * n)
    (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (A H T : ℝ), 0 < Cstar ∧ 0 ≤ A ∧ 1 ≤ H ∧ 1 ≤ T ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, ∃ z ∈ zeroBox481 X H T P, z.1 = r) ∧
          (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  sorry

/-- P0045 page 6, display 10: combine the real and nonreal character cases.
The conclusion remains conditional on the explicit classification and zero region inputs. -/
theorem exceptional_radical481 (hclass : RealPrimitiveStatement481)
    (hzero : RealZeroStatement481) (hiw : IwaniecStatement481)
    (H T : ℝ) (hH : 1 ≤ H) (hT : 1 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
      AdmissibleP131 X P → ∀ z ∈ zeroBox481 X H T P,
        c * Lg X ^ 2 ≤ (oddRad131 z.1 : ℝ) := by
  obtain ⟨cr, hcr, Xr, hr⟩ := real_exceptional_conductor481 hzero H T hH hT
  obtain ⟨cn, hcn, Xn, hn⟩ := nonreal_exceptional_radical481 hiw H T hH hT
  refine ⟨min (cr / 8) cn, lt_min (by positivity) hcn, max Xr Xn, ?_⟩
  intro X hX P hP z hz
  by_cases hreal : ∀ a, (z.2.1 a).im = 0
  · have hbound := real_radical_transfer481 (hclass _ hz.1 _ hz.2.2.1 hreal)
      (hr X ((le_max_left _ _).trans hX) P hP z hz hreal)
    have hm := mul_le_mul_of_nonneg_right (min_le_left (cr / 8) cn) (sq_nonneg (Lg X))
    nlinarith
  · exact (mul_le_mul_of_nonneg_right (min_le_right (cr / 8) cn)
      (sq_nonneg (Lg X))).trans
        (hn X ((le_max_right _ _).trans hX) P hP z hz (by simpa using hreal))

end
end LeanLab.LPZ2007
