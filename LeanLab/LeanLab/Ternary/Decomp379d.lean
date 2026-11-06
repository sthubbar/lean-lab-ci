/-
MMS https://arxiv.org/abs/1610.02017v2, pages 3 and 11 to 12.
Assemble the exact main theorem using the new analytic decompositions.
The existing Theorem 2.1 remains an explicit cited dependency.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379a
import LeanLab.Ternary.Decomp379c

namespace LeanLab.Ternary.MMS.Task379

/-- The explicit majorant supplies the original sieve input from the new split.
MMS page 11 equation 5.1 and page 12. CONDITIONAL ON the two reference mean leaves. -/
theorem sieve_majorant_input_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∃ ρp : ℕ → ℝ,
          (∀ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n ≤ ρp n) ∧
          Hyp1 θ x αp η ρp := by
  obtain ⟨αp, hp, hp29, hFourier⟩ := harman_fourier_input_decomposed θ hθ hθ1
  refine ⟨αp, hp, hp29, ?_⟩
  intro η hη
  obtain ⟨X, hX⟩ := hFourier η hη
  refine ⟨max X 16, ?_⟩
  intro x hx
  refine ⟨Task361.harmanMajorant x, ?_, hX x ((le_max_left _ _).trans hx)⟩
  intro n hn
  apply Task361.primeIndicator_le_harmanMajorant
  have hcut := Task361.interval_above_rough_cutoff ((le_max_right _ _).trans hx) hθ1.le
  have hnlo : ⌈x - x ^ θ / 3⌉₊ ≤ n := (Finset.mem_Icc.mp hn).1
  have hnlo' : (⌈x - x ^ θ / 3⌉₊ : ℝ) ≤ n := by exact_mod_cast hnlo
  exact hcut.trans ((Nat.le_ceil _).trans hnlo')

/-- The exact sealed Theorem 1.1 from three analytic leaves and Theorem 2.1.
MMS pages 3 and 11 to 12. CONDITIONAL ON bhp_endpoint_lower,
harman_reference_mean, harman_fourier_of_reference_mean and mms_thm21.
The elementary interval normalization is proved independently of primes. -/
theorem mms_theorem11_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) :
    AlmostEqualVinogradov θ := by
  let t : ℝ := min θ (3 / 4)
  have ht : 11 / 20 < t := lt_min hθ (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨αp, hp, hp29, hmajor⟩ := sieve_majorant_input_decomposed t ht ht1
  obtain ⟨ε, he, he1, X₂, hminor⟩ := short_progression_input_decomposed t ht ht1
  apply almostEqualVinogradov_mono (min_le_left θ (3 / 4))
  apply almostEqual_of_thm21 mms_thm21 (by linarith : 0 < t) ht1 he he1 hp
    (by norm_num : (0 : ℝ) < 0.99) (by linarith : αp < 3 * 0.99)
  intro η hη
  obtain ⟨X₁, hX₁⟩ := hmajor η hη
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx
  obtain ⟨ρp, hρp, hfourier⟩ := hX₁ x ((le_max_left _ _).trans hx)
  exact ⟨ρp, hρp, hfourier, hminor x ((le_max_right _ _).trans hx)⟩

end LeanLab.Ternary.MMS.Task379
