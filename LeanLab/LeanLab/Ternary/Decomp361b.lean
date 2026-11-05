/-
P0028 https://arxiv.org/abs/1610.02017v2, pages 3 and 11 to 12.
Separate the two analytic inputs used to deduce Theorem 1.1.
The final theorem is CONDITIONAL ON these leaves and mms_thm21.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp361e

namespace LeanLab.Ternary.MMS.Task361

/-- The explicit sieve majorant supplies the Fourier hypothesis with fixed mean below 2.9.
P0028 page 11, equation 5.1 and Proposition 5.1, and page 12, the displays
beginning with the Buchstab integral and ending with condition 1 of Theorem 2.1.
This is the derived unsmoothed hypothesis on the full Theorem 2.1 interval.
The fixed mean is chosen before the Fourier tolerance. -/
theorem sieve_majorant_input (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∃ ρp : ℕ → ℝ,
          (∀ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n ≤ ρp n) ∧
          Hyp1 θ x αp η ρp := by
  obtain ⟨αp, hp, hp29, hFourier⟩ := harman_fourier_input θ hθ hθ1
  refine ⟨αp, hp, hp29, ?_⟩
  intro η hη
  obtain ⟨X, hX⟩ := hFourier η hη
  refine ⟨max X 16, ?_⟩
  intro x hx
  refine ⟨harmanMajorant x, ?_, hX x ((le_max_left _ _).trans hx)⟩
  intro n hn
  apply primeIndicator_le_harmanMajorant
  have hcut := interval_above_rough_cutoff ((le_max_right _ _).trans hx) hθ1.le
  have hnlo : ⌈x - x ^ θ / 3⌉₊ ≤ n := (Finset.mem_Icc.mp hn).1
  have hnlo' : (⌈x - x ^ θ / 3⌉₊ : ℝ) ≤ n := by exact_mod_cast hnlo
  exact hcut.trans ((Nat.le_ceil _).trans hnlo')

/-- LEAF. Primes have lower density 0.99 in every required short progression.
P0028 page 3 below Theorem 2.1, using Baker, Harman and Pintz reference 2,
Theorem 3 part I on page 4, with the totient denominator used by P0028.
The stronger lower constant above 0.9953 on BHP page 41 absorbs endpoint log changes.
The positive loss in the interval exponent is chosen before x. -/
theorem short_progression_input (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Hyp2 θ ε x 0.99 := by sorry

/-- Theorem 1.1 in the exact sealed exponent range, assembled from the two
analytic leaves and the existing Theorem 2.1 input.
P0028 page 3 and pages 11 to 12. CONDITIONAL ON the named inputs. -/
theorem mms_theorem11_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) :
    AlmostEqualVinogradov θ := by
  let t : ℝ := min θ (3 / 4)
  have ht : 11 / 20 < t := lt_min hθ (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨αp, hp, hp29, hmajor⟩ := sieve_majorant_input t ht ht1
  obtain ⟨ε, he, he1, X₂, hminor⟩ := short_progression_input t ht ht1
  apply almostEqualVinogradov_mono (min_le_left θ (3 / 4))
  apply almostEqual_of_thm21 mms_thm21 (by linarith : 0 < t) ht1 he he1 hp
    (by norm_num : (0 : ℝ) < 0.99) (by linarith : αp < 3 * 0.99)
  intro η hη
  obtain ⟨X₁, hX₁⟩ := hmajor η hη
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx
  obtain ⟨ρp, hρp, hfourier⟩ := hX₁ x ((le_max_left _ _).trans hx)
  exact ⟨ρp, hρp, hfourier, hminor x ((le_max_right _ _).trans hx)⟩

end LeanLab.Ternary.MMS.Task361
