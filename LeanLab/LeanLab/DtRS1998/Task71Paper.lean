/-
AI wrote this Lean code for CODEX task71.
P0037 Theorem 2, printed page 206, and Table 1, printed page 213.
The complete computational theorem is a cited Prop. It is not proved here.
Binary Goldbach is open.
-/
import LeanLab.Common.Goldbach

namespace LeanLab.DtRS1998.Task71.Paper

/-- Every even integer in a closed interval is a sum of two primes. -/
def IntervalSum (B L : ℕ) : Prop :=
  ∀ e, B ≤ e → e ≤ B + L → Even e → IsGoldbachSum e

/-- The complete printed Theorem 2, including both interval families. Cited input only. -/
def FullTheorem2 : Prop :=
  (∀ i : ℕ, 3 ≤ i → i ≤ 20 → IntervalSum (10 ^ (5 * i)) (10 ^ 8)) ∧
  (∀ i : ℕ, 20 ≤ i → i ≤ 30 → IntervalSum (10 ^ (10 * i)) (10 ^ 9))

/-- Coverage by the first n entries of a proposed prime list. -/
def CoversPrefix (B L : ℕ) (qs : List ℕ) (n : ℕ) : Prop :=
  ∀ e, B ≤ e → e ≤ B + L → Even e →
    ∃ q ∈ qs.take n, q.Prime ∧ (e - q).Prime

/-- The smallest positive prefix length that covers the interval. -/
def MinimalPrefix (B L : ℕ) (qs : List ℕ) (n : ℕ) : Prop :=
  0 < n ∧ CoversPrefix B L qs n ∧
    ∀ m, 0 < m → m < n → ¬ CoversPrefix B L qs m

/-- A worst case excludes a proposed prefix as a cover of the interval. -/
theorem worst_case_obstruction {B L W n : ℕ} {qs : List ℕ}
    (hlo : B ≤ W) (hhi : W ≤ B + L) (heven : Even W)
    (hbad : ∀ q ∈ qs.take n, q.Prime → ¬ (W - q).Prime) :
    ¬ CoversPrefix B L qs n := by
  intro hcover
  obtain ⟨q, hq, hp, hdiff⟩ := hcover W hlo hhi heven
  exact hbad q hq hp hdiff

end LeanLab.DtRS1998.Task71.Paper
