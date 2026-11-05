import LeanLab.LiuWang2002.ThetaCert352

/-!
Shared prefix verification for Schoenfeld page 356, display 5.1 star.
The Boolean function is executable proof data, not a trust assumption.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352

/-- A scan of consecutive integer primorial comparisons. State n is
the last processed integer, p its primorial, a equals 25 to power n and
b equals 68 to power n. Derived certificate for page 356, display 5.1 star. -/
def thetaScan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, p, a, b =>
    let p' := if 2 ≤ n + 1 ∧ Nat.minFac (n + 1) = n + 1 then p * (n + 1) else p
    decide (p' * (a * 25) < b * 68) && thetaScan k (n + 1) p' (a * 25) (b * 68)

/-- Semantic correctness of the shared prefix scan. A true scan checks
every integer in the requested interval. Derived transfer for page 356,
display 5.1 star. -/
theorem thetaScan_sound (k n : ℕ)
    (hc : thetaScan k n (primorial n) (25 ^ n) (68 ^ n) = true) :
    ∀ m : ℕ, n < m → m ≤ n + k → primorial m * 25 ^ m < 68 ^ m := by
  induction k generalizing n with
  | zero => intro m hm hm'; omega
  | succ k ih =>
    have hp : primorial (n + 1) =
        if (n + 1).Prime then primorial n * (n + 1) else primorial n := by
      rw [primorial_add n 1, Nat.Ico_succ_singleton]
      by_cases hp : (n + 1).Prime
      · rw [Finset.filter_eq_self.mpr (by simpa using hp), Finset.prod_singleton, if_pos hp]
      · rw [Finset.filter_eq_empty_iff.mpr (by simpa using hp), Finset.prod_empty, mul_one, if_neg hp]
    simp only [thetaScan, ← Nat.prime_def_minFac, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [← hp, ← pow_succ, ← pow_succ] at hc
    intro m hm hm'
    by_cases he : m = n + 1
    · simpa [he] using hc.1
    · exact ih (n + 1) hc.2 m (by omega) (by omega)

end LeanLab.LiuWang2002.Task352

#print axioms LeanLab.LiuWang2002.Task352.thetaScan_sound
