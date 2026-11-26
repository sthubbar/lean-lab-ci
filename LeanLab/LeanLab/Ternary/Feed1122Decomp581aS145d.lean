/-
Split of s145c_bucketRoughCount into a prime cofactor part and a two prime
cofactor part. MMS arXiv 1610.02017v2 page 11 bottom display.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp581aS145

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory
attribute [local instance] Classical.propDecidable

/-- The prime cofactor main density, log x over p log of x over p, the u at
most two branch of the Buchstab function at scale x over p. MMS arXiv 1610.02017v2 p. 11 bottom display; new definition, needed to separate the prime cofactor piece. -/
noncomputable def s145d_primeModel (x : ℝ) (p : ℕ) : ℝ :=
  Real.log x / (p * Real.log (x / p))

/-- LEAF: MMS arXiv 1610.02017v2 p. 11 bottom display, prime cofactor part: n = p m in (a,b) with m prime is counted by the short interval prime number theorem at scale x/p, interval length (b-a)/p at least x^(3/4) exp(-sqrt log x) times x^(-1/2), Huxley 1972 or Vinogradov Korobov, single modulus p, as in shortIntervalPNT_scaled of Feed1122Decomp581b. Class HARD. -/
theorem s145d_primePart :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p : ℕ, s145c_lpfAdmissible x p →
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ (n / p).Prime then
            Task361.roughIndicator (n / p) p else 0) -
          (b - a) * s145d_primeModel x p| ≤
        ε * Task379.referenceLength x / p := by
  sorry

/-- LEAF: MMS arXiv 1610.02017v2 p. 11 bottom display, two prime cofactor part: composite m = n/p rough at p with m < p^3 is q1 q2, p <= q1 <= q2; summing the prime count at scale x/(p q1) over q1 gives the Buchstab integral term, bucketModel minus the prime model. Class HARD. -/
theorem s145d_twoPrimePart :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p : ℕ, s145c_lpfAdmissible x p →
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ ¬(n / p).Prime then
            Task361.roughIndicator (n / p) p else 0) -
          (b - a) * (s145c_bucketModel x p - s145d_primeModel x p)| ≤
        ε * Task379.referenceLength x / p := by
  sorry

/-- Exact decomposition of the bucket count into prime and non prime cofactors. -/
theorem s145d_split_sum (x : ℝ) (p : ℕ) (a b : ℝ) :
    (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            Task361.roughIndicator (n / p) p else 0) =
      (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ (n / p).Prime then
            Task361.roughIndicator (n / p) p else 0) +
      (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ ¬(n / p).Prime then
            Task361.roughIndicator (n / p) p else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h1 : p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b
  · obtain ⟨h1, h2, h3⟩ := h1
    by_cases hq : (n / p).Prime <;> simp [h1, h2, h3, hq]
  · by_cases hq : (n / p).Prime
    · simp only [if_neg h1]
      rw [if_neg (fun h => h1 ⟨h.1, h.2.1, h.2.2.1⟩),
        if_neg (fun h => h1 ⟨h.1, h.2.1, h.2.2.1⟩)]; simp
    · simp only [if_neg h1]
      rw [if_neg (fun h => h1 ⟨h.1, h.2.1, h.2.2.1⟩),
        if_neg (fun h => h1 ⟨h.1, h.2.1, h.2.2.1⟩)]; simp

theorem s145c_bucketRoughCount_of_s145d_leaves :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ p : ℕ, s145c_lpfAdmissible x p →
      ∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b then
            Task361.roughIndicator (n / p) p else 0) -
          (b - a) * s145c_bucketModel x p| ≤
        ε * Task379.referenceLength x / p := by
  intro ε hε
  obtain ⟨X1, h1⟩ := s145d_primePart (ε / 2) (by positivity)
  obtain ⟨X2, h2⟩ := s145d_twoPrimePart (ε / 2) (by positivity)
  refine ⟨max X1 X2, fun x hx p hp a b ha hab hb => ?_⟩
  have e1 := h1 x ((le_max_left _ _).trans hx) p hp a b ha hab hb
  have e2 := h2 x ((le_max_right _ _).trans hx) p hp a b ha hab hb
  rw [s145d_split_sum]
  set P := (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ (n / p).Prime then
            Task361.roughIndicator (n / p) p else 0)
  set T := (∑ n ∈ ints x (x + Task379.referenceLength x),
          if p ∣ n ∧ a < (n : ℝ) ∧ (n : ℝ) < b ∧ ¬(n / p).Prime then
            Task361.roughIndicator (n / p) p else 0)
  have key : Real.log x * (P + T) - (b - a) * s145c_bucketModel x p =
      (Real.log x * P - (b - a) * s145d_primeModel x p) +
      (Real.log x * T - (b - a) * (s145c_bucketModel x p - s145d_primeModel x p)) := by ring
  rw [key]
  calc _ ≤ |Real.log x * P - (b - a) * s145d_primeModel x p| +
        |Real.log x * T - (b - a) * (s145c_bucketModel x p - s145d_primeModel x p)| :=
          abs_add_le _ _
    _ ≤ ε / 2 * Task379.referenceLength x / p + ε / 2 * Task379.referenceLength x / p :=
          add_le_add e1 e2
    _ = ε * Task379.referenceLength x / p := by ring

end LeanLab.Ternary.MMS.Task581
