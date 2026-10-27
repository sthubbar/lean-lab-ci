import LeanLab.Ricci1937.CPrimeUpper

/-!
Elementary prime pair count for the identity case of Ricci 1937, page 74.
These estimates count products, with no assertion of a new result.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset Real Filter
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The large factor block used in the count. -/
def ricciPrimeBlock (n : ℕ) (α : ℝ) : Finset ℕ :=
  (Nat.primesLE n).filter fun p =>
    (n : ℝ) ^ α ≤ p ∧ (p : ℝ) ≤ (n : ℝ) ^ (1 - α)

/-- Products with the first factor in the large block and product at most n. -/
def ricciPrimePairValues (n : ℕ) (α : ℝ) : Finset ℕ :=
  (ricciPrimeBlock n α).biUnion fun p => (Nat.primesLE (n / p)).image fun q => p * q

/-- Counting ordered representations bounds the number of distinct products. -/
lemma ricciPrimePairValues_card_le (n : ℕ) (α : ℝ) :
    #(ricciPrimePairValues n α) ≤ ∑ p ∈ ricciPrimeBlock n α, (n / p).primeCounting := by
  apply (card_biUnion_le).trans
  apply sum_le_sum
  intro p _
  exact (card_image_le).trans_eq (Nat.primesLE_card_eq_primeCounting _)

/-- The large block pair count has order at most n over log n. -/
theorem ricciPrimePairValues_upper {α : ℝ} (hα : 0 < α) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      (#(ricciPrimePairValues n α) : ℝ) ≤ D * n / Real.log n := by
  obtain ⟨K, hK, hupper⟩ := ricci_primeCounting_upper
  obtain ⟨X, hX⟩ := eventually_atTop.mp hupper
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  refine ⟨2 * K / α ^ 2, by positivity, ?_⟩
  filter_upwards [htend.eventually (eventually_ge_atTop X), eventually_ge_atTop 4] with n hnX hn4
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hblock : ricciPrimeBlock n α ⊆ Nat.primesLE n := filter_subset _ _
  have hsum := ricci_prime_block_reciprocals n hn4 (ricciPrimeBlock n α) hblock hα
    (fun p hp => (mem_filter.mp hp).2.1)
  have hterm : ∀ p ∈ ricciPrimeBlock n α,
      ((n / p).primeCounting : ℝ) ≤ (K / α) * ((n : ℝ) / Real.log n) * (1 / p) := by
    intro p hp
    have hprime := Nat.mem_primesLE.mp (hblock hp) |>.2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpmax := (mem_filter.mp hp).2.2
    apply ricci_primeCounting_div_le (by omega) hprime hK.le hα hpmax
    exact hX _ (hnX.trans (ricci_complementary_power (by linarith) hpR hpmax))
  calc
    (#(ricciPrimePairValues n α) : ℝ) ≤
        ∑ p ∈ ricciPrimeBlock n α, ((n / p).primeCounting : ℝ) := by
      exact_mod_cast ricciPrimePairValues_card_le n α
    _ ≤ ∑ p ∈ ricciPrimeBlock n α,
        (K / α) * ((n : ℝ) / Real.log n) * (1 / p) := sum_le_sum hterm
    _ = (K / α) * ((n : ℝ) / Real.log n) *
        ∑ p ∈ ricciPrimeBlock n α, (1 / p : ℝ) := by rw [mul_sum]
    _ ≤ (K / α) * ((n : ℝ) / Real.log n) * (2 / α) := by gcongr
    _ = (2 * K / α ^ 2) * n / Real.log n := by ring

example : #(ricciPrimePairValues 100 ((1 : ℝ) / 6)) ≤
    ∑ p ∈ ricciPrimeBlock 100 ((1 : ℝ) / 6), (100 / p).primeCounting :=
  ricciPrimePairValues_card_le 100 ((1 : ℝ) / 6)

end
end LeanLab.Ricci1937
