/-
AI wrote this Lean code for CODEX task51.
P0074 pages 6 and 7, a coarse variant of the Proposition 2.1 second moment.
This global-energy bound does not discharge ShortSecondMoment.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Lemma31Proof

namespace LeanLab.Grimmelt2019.Prop21
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A reflected translate of a supported sequence has squared mass at most its full mass. -/
theorem shifted_sqn_le (S : Finset ℤ) (g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    ∑ m ∈ S, g (n - m) ^ 2 ≤ sqn S g := by
  let T := S.filter (fun m => n - m ∈ S)
  have hfilter : (∑ m ∈ S, g (n - m) ^ 2) = ∑ m ∈ T, g (n - m) ^ 2 := by
    dsimp only [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h : n - m ∈ S
    · simp [h]
    · simp [h, hg (n - m) h]
  have himage : (∑ k ∈ T.image (fun m => n - m), g k ^ 2) = ∑ m ∈ T, g (n - m) ^ 2 := by
    exact Finset.sum_image (fun a ha b hb hab => by omega)
  have hsub : T.image (fun m => n - m) ⊆ S := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_filter.mp hm).2
  rw [hfilter, ← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

/-- Pointwise convolution is bounded by the product of the two full squared norms. -/
theorem conv_sq_le_global (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (n : ℤ) :
    conv S f g n ^ 2 ≤ sqn S f * sqn S g := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S f (fun m => g (n - m))
  apply hcs.trans
  exact mul_le_mul_of_nonneg_left (shifted_sqn_le S g hg n) (sqn_nonneg S f)

/-- Summing the coarse pointwise inequality costs the exact number of endpoints. -/
theorem secondMoment_card_le (S : Finset ℤ) (f g : ℤ → ℝ) (hg : SuppIn S g) (X H : ℝ) :
    (∑ n ∈ win X H, conv S f g n ^ 2) ≤ ((win X H).card : ℝ) * sqn S f * sqn S g := by
  calc
    _ ≤ ∑ _n ∈ win X H, sqn S f * sqn S g := by
      apply Finset.sum_le_sum
      intro n hn
      exact conv_sq_le_global S f g hg n
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The unconditional coarse short second moment retains global g energy in place of local Fourier energy. -/
theorem shortSecondMoment_global_energy (S : Finset ℤ) (f g : ℤ → ℝ)
    (hg : SuppIn S g) (X H : ℝ) (hH : 1 ≤ H) :
    (∑ n ∈ win X H, conv S f g n ^ 2) ≤ 2 * H * sqn S f * sqn S g := by
  have hc := (abs_le.mp (MainTerm.shortInterval_card_error (t := X) (show 0 ≤ H by linarith))).2
  have hcard : ((win X H).card : ℝ) ≤ 2 * H := by
    change ((win X H).card : ℝ) - H ≤ 1 at hc
    linarith
  apply (secondMoment_card_le S f g hg X H).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (sqn_nonneg S f)) (sqn_nonneg S g)

#print axioms shifted_sqn_le
#print axioms conv_sq_le_global
#print axioms secondMoment_card_le
#print axioms shortSecondMoment_global_energy
end LeanLab.Grimmelt2019.Prop21
