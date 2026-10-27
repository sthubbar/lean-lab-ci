/-
AI-written Lean code, Gemini, 2026-10-22, unit U-0259.
Unformalized statements from the literature: the prime k-tuples upper bound and the
prime k-tuples conjecture (Hardy-Littlewood).
-/
import Mathlib

open Finset Nat Real

namespace LeanLab.BrunGap

/-- A set of integers is admissible if for every prime p, it does not cover all congruence classes mod p. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (H.image (fun h => h % p)).card < p

/-- The number of integers `n < N` such that `n + h` is prime for all `h ∈ H`. -/
noncomputable def kTupleCount (H : Finset ℕ) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => ∀ h ∈ H, (n + h).Prime)).card

/-- The prime k-tuples upper bound from sieve methods. -/
def KTupleUpper : Prop :=
  ∀ H : Finset ℕ, H.Nonempty → Admissible H →
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → (kTupleCount H N : ℝ) ≤ C * N / Real.log N ^ H.card

/-- The prime k-tuples conjecture (Hardy-Littlewood). -/
def KTupleConjecture : Prop :=
  ∀ H : Finset ℕ, H.Nonempty → Admissible H →
    ∀ N : ℕ, ∃ n ≥ N, ∀ h ∈ H, (n + h).Prime

end LeanLab.BrunGap
