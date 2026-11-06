/-
P0093 page 168 equation 10.5. An explicit reciprocal square tail bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Linnik1951

open Finset

/-- P0093 page 168 equation 10.5. The prime reciprocal square tail is
bounded by the tail over every integer after shifting the prime by one. -/
theorem prime_reciprocal_square_cutoff439 (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑' p : Nat.Primes,
      if Q < (p : ℕ) then 1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤ 2 / (Q : ℝ) := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro p
    dsimp only
    split_ifs <;> positivity
  intro s
  rw [← Finset.sum_filter]
  let t := s.filter (fun p : Nat.Primes => Q < (p : ℕ))
  let M := t.sup (fun p => (p : ℕ))
  have hinj : Set.InjOn (fun p : Nat.Primes => (p : ℕ) - 1) (t : Set Nat.Primes) := by
    intro p hp q hq heq
    change (p : ℕ) - 1 = (q : ℕ) - 1 at heq
    apply Subtype.ext
    have := p.property.two_le
    have := q.property.two_le
    omega
  have hsub : t.image (fun p : Nat.Primes => (p : ℕ) - 1) ⊆ Ioo (Q - 1) (M + 1) := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hqp := (Finset.mem_filter.mp hp).2
    have hpM : (p : ℕ) ≤ M := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp
    simp only [Finset.mem_Ioo]
    omega
  calc
    _ = ∑ p ∈ t, ((((p : ℕ) - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.cast_sub p.property.one_le, Nat.cast_one]
      simp only [one_div]
    _ = ∑ m ∈ t.image (fun p : Nat.Primes => (p : ℕ) - 1), ((m : ℝ) ^ 2)⁻¹ :=
      (Finset.sum_image (f := fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) hinj).symm
    _ ≤ ∑ m ∈ Ioo (Q - 1) (M + 1), ((m : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / (((Q - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (Q - 1) (M + 1)
    _ = 2 / (Q : ℝ) := by rw [Nat.cast_sub hQ, Nat.cast_one]; ring

/-- P0093 page 168 equation 10.5. Exact sealed prime_reciprocal_square_tail357
statement. The estimate already holds as soon as N is at least one. -/
theorem prime_reciprocal_square_tail_proved439 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      (∑' p : Nat.Primes,
        if ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ < (p : ℕ) then
          1 / (((p : ℕ) : ℝ) - 1) ^ 2 else 0) ≤
        2 / ((⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊ : ℝ)) := by
  refine ⟨0, fun N hN => prime_reciprocal_square_cutoff439 _ ?_⟩
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)

end LeanLab.Linnik1951
