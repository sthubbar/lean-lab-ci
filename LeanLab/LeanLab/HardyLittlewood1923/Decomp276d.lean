/-
AI wrote this Lean code for CODEX task276.
P0004 page 64 Theorem X 2 and its immediate proof.
The recurrence statement is CONDITIONAL on Hypothesis X.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.Section5

namespace LeanLab.HardyLittlewood1923.Decomp276d

open Finset
open LeanLab.HardyLittlewood1923.Section5

/-- P0004 page 64 Theorem X 2, the finite admissibility criterion.
Only primes at most the size of the pattern need to be checked.
This theorem uses the lab's missing residue meaning of Possible. -/
theorem possible_of_small_primes (b : Finset ℕ)
    (hb : ∀ q : ℕ, q.Prime → q ≤ b.card → ∃ a < q, ∀ x ∈ b, x % q ≠ a) :
    Possible b := by
  intro q hq
  by_cases h : q ≤ b.card
  · exact hb q hq h
  · exact possible_of_card_lt b q hq.pos (lt_of_not_ge h)

/-- P0004 page 64 Theorem X 2. A singleton supplies a concrete admissible pattern. -/
theorem singleton_possible : Possible ({0} : Finset ℕ) := by
  exact possible_of_small_primes {0} (by simp only [card_singleton]; intro q hq h; have := hq.two_le; omega)

/-- P0004 page 65 proof of equation 5.6913.
A set with at most mu elements, all avoiding primes at most mu, is admissible. -/
theorem possible_of_sifted (b : Finset ℕ) (μ : ℕ) (hcard : b.card ≤ μ)
    (hs : ∀ q : ℕ, q.Prime → q ≤ μ → ∀ x ∈ b, ¬ q ∣ x) : Possible b := by
  exact possible_of_small_primes b (fun q hq hqb =>
    ⟨0, hq.pos, fun x hx heq => hs q hq (hqb.trans hcard) x hx (Nat.dvd_of_mod_eq_zero heq)⟩)

/-- P0004 pages 64 and 65, the possible groups used in equation 5.6913.
Translation preserves the missing residue condition. -/
theorem possible_translate_iff (n : ℕ) (b : Finset ℕ) :
    Possible (b.image (fun x => n + x)) ↔ Possible b := by
  constructor
  · intro h q hq
    obtain ⟨a, ha, hm⟩ := h q hq
    let c := a + q - n % q
    refine ⟨c % q, Nat.mod_lt _ hq.pos, fun x hx heq => ?_⟩
    have hc : (n + c % q) % q = a := by
      have hnq := Nat.mod_lt n hq.pos
      calc _ = (n % q + c) % q := by simp [Nat.add_mod]
           _ = (a + q) % q := by congr 1; dsimp [c]; omega
           _ = a := by simp [Nat.mod_eq_of_lt ha]
    have hh : (n + x) % q = a := by
      calc _ = (n % q + x % q) % q := Nat.add_mod _ _ _
           _ = (n % q + c % q) % q := by rw [heq]
           _ = (n + c % q) % q := by simp [Nat.add_mod]
           _ = a := hc
    exact hm (n + x) (mem_image.mpr ⟨x, hx, rfl⟩) hh
  · intro h q hq
    obtain ⟨a, ha, hm⟩ := h q hq
    refine ⟨(n + a) % q, Nat.mod_lt _ hq.pos, ?_⟩
    intro y hy heq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    have hxa : Nat.ModEq q x a := Nat.ModEq.add_left_cancel' n heq
    exact hm x hx (by simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha] using hxa)

/-- P0004 page 65 equation 5.6913, the offset pattern version of the elementary step.
No prime tuple hypothesis is needed for admissibility. -/
theorem possible_of_sifted_translate (n : ℕ) (b : Finset ℕ) (μ : ℕ) (hcard : b.card ≤ μ)
    (hs : ∀ q : ℕ, q.Prime → q ≤ μ → ∀ x ∈ b, ¬ q ∣ n + x) : Possible b := by
  apply (possible_translate_iff n b).mp
  apply possible_of_sifted (b.image (fun x => n + x)) μ (card_image_le.trans hcard)
  intro q hq hqμ y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  exact hs q hq hqμ x hx

/-- P0004 page 64 Theorem X 2 in the paper's recurrence meaning.
CONDITIONAL on the prime tuple assertion of Hypothesis X, given as hX. -/
theorem recurrence_of_small_primes
    (hX : ∀ b : Finset ℕ, Possible b → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ ∀ x ∈ b, (n + x).Prime)
    (b : Finset ℕ)
    (hb : ∀ q : ℕ, q.Prime → q ≤ b.card → ∃ a < q, ∀ x ∈ b, x % q ≠ a)
    (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ ∀ x ∈ b, (n + x).Prime := by
  exact hX b (possible_of_small_primes b hb) N

#print axioms possible_of_sifted_translate
#print axioms possible_of_sifted
#print axioms possible_translate_iff
#print axioms possible_of_small_primes
#print axioms singleton_possible
#print axioms recurrence_of_small_primes

end LeanLab.HardyLittlewood1923.Decomp276d
