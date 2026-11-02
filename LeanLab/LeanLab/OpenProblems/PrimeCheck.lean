import Mathlib

/-!
# OpenProblems, a kernel primality check shared by the open problem files

Unit U-1603. AI wrote the Lean code. Helper only, no open problem is stated here. `primeB B n` is
trial division by every `d < B` with `d * d ≤ n`, and `primeB_iff` proves it correct whenever
`n < B * B`. Written with `List.all` so that `decide +kernel` evaluates it through the kernel's
fast `Nat` operations, with no `native_decide` and so no extra axiom.
-/

namespace LeanLab.OpenProblems

/-- Trial division primality test, correct for `n < B * B` by `primeB_iff`. -/
def primeB (B n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range B).all fun d => decide (d < 2) || decide (n < d * d) || decide (n % d ≠ 0)

theorem primeB_iff {B n : ℕ} (h : n < B * B) : primeB B n = true ↔ n.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun m hm hle hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hle
    have hmB : m < B := by
      by_contra hc
      have : B * B ≤ m * m := Nat.mul_le_mul (not_lt.mp hc) (not_lt.mp hc)
      omega
    rcases hall m hmB with (h1 | h1) | h1
    · omega
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d _ => ?_⟩
    by_cases hd : d < 2
    · exact Or.inl (Or.inl hd)
    by_cases hdn : n < d * d
    · exact Or.inl (Or.inr hdn)
    · refine Or.inr fun h0 => hall d (not_lt.mp hd) (Nat.le_sqrt.mpr (not_lt.mp hdn))
        (Nat.dvd_of_mod_eq_zero h0)

end LeanLab.OpenProblems

#print axioms LeanLab.OpenProblems.primeB_iff
