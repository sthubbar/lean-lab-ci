import LeanLab.AlmostPrimes.CampbellCase2X
import LeanLab.AlmostPrimes.DDNathanson

/-!
AI wrote the Lean code. Goldbach is open.
Campbell 2026 v1, arXiv 2608.09488, Section 3, printed page 4.
The displayed three-case formula after equation 3.2 counts the pre-sieved indices.
-/

open Finset

namespace LeanLab.AlmostPrimes.CampbellCount
open Campbell2026 CampbellCase2X

/-- Natural number form of the exact count on Campbell page 4. -/
theorem Xcount_exact (N : ℕ) (hN : 2 ≤ N) :
    Xcount N = if N % 3 = 0 then 2 * (N / 3) else (N + 1) / 3 := by
  let P : ℕ → Prop := fun n => n % 3 ≠ 0 ∧ n % 3 ≠ N % 3
  have hdvd (n : ℕ) (hn : n ≤ N) :
      3 ∣ aSeq N n ↔ n % 3 = 0 ∨ n % 3 = N % 3 := by
    simpa [DDNathanson.Q, DDNathanson.mp, DDNathanson.ep] using
      DDNathanson.dvd_aSeq_iff Nat.prime_three hn
  have heq : Xcount N = Nat.count P N := by
    rw [Nat.count_eq_card_filter_range]
    unfold Xcount
    congr 1
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, hn⟩
      refine ⟨by omega, ?_⟩
      rw [hdvd n (by omega)] at hn
      exact not_or.mp hn
    · rintro ⟨hn, hp⟩
      have hn1 : 1 ≤ n := by
        have hp0 : n % 3 ≠ 0 := hp.1
        omega
      refine ⟨⟨hn1, by omega⟩, ?_⟩
      rw [hdvd n (by omega)]
      exact not_or.mpr hp
  have hper : ∀ n, P (n + 3) ↔ P n := by
    intro n
    simp [P]
  have hmul (q : ℕ) : Nat.count P (3 * q) = q * Nat.count P 3 := by
    induction q with
    | zero => simp
    | succ q ih =>
      calc Nat.count P (3 * (q + 1)) = Nat.count P (3 + 3 * q) := by congr 1 <;> omega
        _ = Nat.count P 3 + Nat.count P (3 * q) :=
          DDNathanson.count_add_period P 3 hper (3 * q)
        _ = (q + 1) * Nat.count P 3 := by rw [ih]; ring
  have hshift : (fun k => P (3 * (N / 3) + k)) = P := by
    funext k
    apply propext
    simp [P, Nat.add_mod]
  have hsplit : Nat.count P N = (N / 3) * Nat.count P 3 + Nat.count P (N % 3) := by
    calc Nat.count P N = Nat.count P (3 * (N / 3) + N % 3) := by congr 1 <;> omega
      _ = Nat.count P (3 * (N / 3)) + Nat.count (fun k => P (3 * (N / 3) + k)) (N % 3) :=
        Nat.count_add P _ _
      _ = _ := by simp only [hshift, hmul]
  rw [heq, hsplit]
  rcases (by omega : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2) with h | h | h
  · simp [h, P, Nat.count_succ, Nat.count_zero, Nat.mul_comm]
  · simp [h, P, Nat.count_succ, Nat.count_zero]
    omega
  · simp [h, P, Nat.count_succ, Nat.count_zero]
    omega

/-- The exact real-valued three-case formula printed in the paper. -/
theorem Xcount_exact_real (N : ℕ) (hN : 2 ≤ N) :
    (Xcount N : ℝ) = if N % 3 = 0 then 2 * (N : ℝ) / 3
      else if N % 3 = 1 then ((N : ℝ) - 1) / 3 else ((N : ℝ) + 1) / 3 := by
  have hc := Xcount_exact N hN
  by_cases h0 : N % 3 = 0
  · rw [ite_eq_left h0] at hc ⊢
    have h : 3 * Xcount N = 2 * N := by omega
    have hr : (3 : ℝ) * Xcount N = 2 * N := by exact_mod_cast h
    linarith
  · rw [ite_eq_right h0] at hc ⊢
    by_cases h1 : N % 3 = 1
    · rw [ite_eq_left h1]
      have h : 3 * Xcount N + 1 = N := by omega
      have hr : (3 : ℝ) * Xcount N + 1 = N := by exact_mod_cast h
      linarith
    · rw [ite_eq_right h1]
      have h : 3 * Xcount N = N + 1 := by omega
      have hr : (3 : ℝ) * Xcount N = N + 1 := by exact_mod_cast h
      linarith

example : Xcount 3 = 2 := by
  rw [Xcount_exact 3 (by decide)]
  norm_num

end LeanLab.AlmostPrimes.CampbellCount

#print axioms LeanLab.AlmostPrimes.CampbellCount.Xcount_exact
#print axioms LeanLab.AlmostPrimes.CampbellCount.Xcount_exact_real
