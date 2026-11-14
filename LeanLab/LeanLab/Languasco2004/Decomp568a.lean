/-
Jia 1996 pages 263 and 277 to 279, displays 48 and 53 to 56.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The source prime transfer and model asymptotic remain OPEN.
-/
import LeanLab.Languasco2004.Numeric568
import LeanLab.Languasco2004.GroupSplit548
namespace LeanLab.Languasco2004.Decomp568a
open Finset Real Decomp279a Decomp316a GroupSplit548 Numeric568
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 263 display 48: the integer model count S of B_d and z.
The model sifts all primes and has no primality condition on a complement. -/
def modelSifted (Y : ℝ) (d : ℕ) (z : ℝ) : ℕ :=
  ((Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun a => d ∣ a ∧
    ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬ p ∣ a)).card

/-- Page 279: the integer model for the selected Omega4 region.
The fixed cap exceeds both prime indices on the source domain. -/
def model4 (Y : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
      Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
    ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
      (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
      (modelSifted Y (p * q) q : ℝ)

/-- Page 279: the real coefficient of the complete Omega4 integral. -/
def integral4 : ℝ := ∫ t in (41 / 180 : ℝ)..(8 / 33), inner4 t

/-- LEAF. Page 279 after displays 53 to 56, using Lemma 21 on page 262.
Only the all integer model is compared with its Buchstab integral.
No prime complementary variable or exceptional set occurs in this leaf. -/
theorem model4_asymptotic :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (integral4 - η) * (Y / Real.log Y) ≤ model4 Y := by sorry

/-- LEAF. Pages 277 to 279, displays 53 to 56 and the exception convention
before display 48 on page 263. This is the prime to integer model transfer.
The written proof uses Lemmas 13, 17, 18 and 19 and the Iwaniec sieve.
The discrepancy exceptional set is bounded before any numerical coefficient is used. -/
theorem region4_transfer_exception :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        η * scale N (localization N ε) n <
        |pieceSum 3 4 true N (localization N ε) n -
          singular n / Real.log N * model4 (localization N ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Page 279 numerical support: the coefficient has a half micro unit reserve. -/
theorem integral4_reserve : (0.0096365 : ℝ) ≤ integral4 := region4_numeric_margin

/-- LEAF. Page 279: localization eventually exceeds every fixed model threshold. -/
theorem localization_eventually (ε T : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → T ≤ localization N ε  := by
  have h := tendsto_rpow_atTop (by linarith : (0 : ℝ) < 7 / 12 + ε)
  exact Filter.eventually_atTop.mp (h.eventually (Filter.eventually_ge_atTop T))


/-- Page 279: the exact sealed region4_lower statement follows from
its model asymptotic, its prime transfer and the proved numerical reserve.
CONDITIONAL ON the two OPEN analytic leaves above. -/
theorem region4_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n => pieceSum 3 4 true N (localization N ε) n <
        0.009636 * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e, he, htransfer⟩ := region4_transfer_exception 0.00000025 (by norm_num)
  refine ⟨e, he, ?_⟩
  intro ε B hε heε hB
  obtain ⟨C, N1, hC⟩ := htransfer ε B hε heε hB
  obtain ⟨Y0, hY0⟩ := model4_asymptotic 0.00000025 (by norm_num)
  obtain ⟨N2, hN2⟩ := localization_eventually ε Y0 hε
  refine ⟨C, max 2 (max N1 N2), ?_⟩
  intro N hN
  have hN1 : N1 ≤ N := (le_max_left N1 N2).trans ((le_max_right _ _).trans hN)
  have hN2' : N2 ≤ N := (le_max_right N1 N2).trans ((le_max_right _ _).trans hN)
  have hNpos : 1 < N := by have := (le_max_left 2 (max N1 N2)).trans hN; linarith
  have hY : 1 ≤ localization N ε := Real.one_le_rpow hNpos.le (by linarith : (0 : ℝ) ≤ 7 / 12 + ε)
  have hsub : (window N ε).filter (fun n => pieceSum 3 4 true N (localization N ε) n <
      0.009636 * scale N (localization N ε) n) ⊆
      (window N ε).filter (fun n => 0.00000025 * scale N (localization N ε) n <
        |pieceSum 3 4 true N (localization N ε) n -
          singular n / Real.log N * model4 (localization N ε)|) := by
    intro n hn
    obtain ⟨hnw, hn⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hnw, ?_⟩
    by_contra h
    push Not at h
    have hl := (abs_le.mp h).1
    have hm := mul_le_mul_of_nonneg_left (hY0 _ (hN2 _ hN2'))
      (div_nonneg (singular_nonneg n) (Real.log_nonneg hNpos.le))
    have heq : singular n / Real.log N * ((integral4 - 0.00000025) *
        (localization N ε / Real.log (localization N ε))) =
        (integral4 - 0.00000025) * scale N (localization N ε) n := by
      unfold scale
      ring
    rw [heq] at hm
    have hs := scale_nonneg n hNpos.le hY
    have hi := mul_le_mul_of_nonneg_right integral4_reserve hs
    nlinarith
  exact (show (((window N ε).filter (fun n => pieceSum 3 4 true N (localization N ε) n <
      0.009636 * scale N (localization N ε) n)).card : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans (hC N hN1)

#print axioms integral4_reserve
#print axioms localization_eventually
#print axioms model4_asymptotic
#print axioms region4_transfer_exception
#print axioms region4_lower_from_parts
end
end LeanLab.Languasco2004.Decomp568a
