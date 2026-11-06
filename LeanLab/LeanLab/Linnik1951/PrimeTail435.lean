/-
P0093 page 168. Elementary reciprocal square tails for a fresh main input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_singular_tail357

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 reciprocal square summation in equation 10.5.
The tail over all natural denominators at least a positive K is at
most two over K. Reuse Mathlib sum_Ioo_inv_sq_le. -/
theorem reciprocal_square_nat_tail435 (K : ℕ) (hK : 1 ≤ K) :
    (∑' n : ℕ, if K ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) ≤ 2 / (K : ℝ) := by
  classical
  apply Real.tsum_le_of_sum_range_le (fun n => by split_ifs <;> positivity)
  intro n
  rw [← Finset.sum_filter]
  have he : ((range n).filter (fun i => K ≤ i)) = Ioo (K - 1) n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    omega
  rw [he]
  have hb := sum_Ioo_inv_sq_le (α := ℝ) (K - 1) n
  have hc : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel hK
  rw [hc] at hb
  simpa only [one_div] using hb

/-- P0093 page 168 reciprocal square tail in equation 10.5.
The sum over primes beyond a positive integer cutoff K is at most
two over K, by the injective map p to p minus one and the natural tail. -/
theorem reciprocal_square_prime_tail435 (K : ℕ) (hK : 1 ≤ K) :
    (∑' p : Nat.Primes, if K < (p : ℕ) then
      1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤ 2 / (K : ℝ) := by
  classical
  let f : ℕ → ℝ := fun n => if K ≤ n then 1 / (n : ℝ) ^ 2 else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by dsimp [f]; split_ifs <;> positivity)
      (fun n => ?_) (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    dsimp [f]
    split_ifs
    · exact le_rfl
    · positivity
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    change (p : ℕ) - 1 = (q : ℕ) - 1 at hpq
    omega
  have he (p : Nat.Primes) : (if K < (p : ℕ) then
      1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) = f ((p : ℕ) - 1) := by
    have hp := p.property.two_le
    have hiff : K < (p : ℕ) ↔ K ≤ (p : ℕ) - 1 := by omega
    have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) = ((p : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ (p : ℕ)), Nat.cast_one]
    simp only [f, hiff, hcast]
  simp_rw [he]
  calc
    _ ≤ ∑' n : ℕ, f n := (hf.comp_injective hi).tsum_le_tsum_of_inj
      (fun p : Nat.Primes => (p : ℕ) - 1) hi
      (fun n _ => by dsimp [f]; split_ifs <;> positivity) (fun p => le_rfl) hf
    _ ≤ _ := reciprocal_square_nat_tail435 K hK

/-- P0093 page 168 equation 10.5. Exact
prime_reciprocal_square_tail357 statement from the elementary integer
cutoff tail. The cutoff is positive for every N greater than one. -/
theorem prime_reciprocal_square_tail_proved435 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      (∑' p : Nat.Primes,
        if ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ < (p : ℕ) then
          1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤
        2 / ((⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ)) := by
  refine ⟨1, ?_⟩
  intro N hN
  apply reciprocal_square_prime_tail435
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hN.le) (by norm_num)

end LeanLab.Linnik1951
