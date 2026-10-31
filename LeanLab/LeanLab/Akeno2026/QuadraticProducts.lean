/-
P0087 Akeno 2026 Lemma 4.6 page 34.
Uniform finite product comparisons retain the possible prime 5 factor.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.QuadraticSieve

namespace LeanLab.Akeno2026.QuadraticSieve
open Finset

theorem lower_factor_bounds {p : ℕ} (h5 : 5 ≤ p) :
    (1 / 3 : ℝ) ≤ 1 - 2 / ((p : ℝ) - 2) ∧ 1 - 2 / ((p : ℝ) - 2) ≤ 1 := by
  have hP : (5 : ℝ) ≤ p := by exact_mod_cast h5
  have h0 : 0 ≤ 2 / ((p : ℝ) - 2) := div_nonneg (by norm_num) (by linarith)
  have h1 : 2 / ((p : ℝ) - 2) ≤ 2 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  constructor <;> linarith

theorem density_product_lower (N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    (∏ p ∈ S, (1 - 2 / ((p : ℝ) - 2))) ≤ ∏ p ∈ S, (1 - gDensity N p) := by
  apply Finset.prod_le_prod₀
  · intro p hp
    exact le_trans (by norm_num) (lower_factor_bounds (hS p hp).2).1
  · intro p hp
    have h := (gDensity_bounds N p (hS p hp).1 (hS p hp).2).2
    linarith

theorem density_product_lower_erase_five (N : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    (1 / 3 : ℝ) * (∏ p ∈ S.erase 5, (1 - 2 / ((p : ℝ) - 2))) ≤
      ∏ p ∈ S, (1 - gDensity N p) := by
  have hprod := density_product_lower N S hS
  by_cases h5 : 5 ∈ S
  · have he := Finset.mul_prod_erase S (fun p : ℕ => (1 : ℝ) - 2 / ((p : ℝ) - 2)) h5
    norm_num at he
    linarith
  · rw [Finset.erase_eq_of_notMem h5]
    have hn : 0 ≤ ∏ p ∈ S, ((1 : ℝ) - 2 / ((p : ℝ) - 2)) := by
      apply Finset.prod_nonneg
      intro p hp
      exact le_trans (by norm_num) (lower_factor_bounds (hS p hp).2).1
    linarith

theorem omegaCount_twelve_five : omegaCount 12 5 = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := omegaCount_eq_legendre 5 (by decide) 12
  have hl : legendreSym 5 (12 ^ 2 + 2) = 1 :=
    (legendreSym.eq_one_iff 5 (by decide +kernel)).mpr ⟨1, by decide +kernel⟩
  rw [hl] at h
  exact_mod_cast h

theorem gDensity_twelve_five : gDensity 12 5 = (2 / 3 : ℝ) := by
  rw [gDensity, ite_eq_right (by decide)]
  norm_num only [Nat.cast_ofNat]
  rw [omegaCount_twelve_five]
  rw [psiN_prime_not_dvd (by decide) (by decide)]
  norm_num

/-- Omitting the prime 5 factor is not a uniform finite product inequality. -/
theorem omitted_five_counterexample :
    ¬ (∏ p ∈ ({5} : Finset ℕ).erase 5, ((1 : ℝ) - 2 / ((p : ℝ) - 2))) ≤
      ∏ p ∈ ({5} : Finset ℕ), (1 - gDensity 12 p) := by
  norm_num [gDensity_twelve_five]

end LeanLab.Akeno2026.QuadraticSieve
