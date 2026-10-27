/-
P0017 p. 1745 abstract and p. 1747 Section 4.
The reported computation checked even integers through 4 * 10^14.
The largest smaller prime in a minimal partition was 5569.
The leaves separate finite search correctness from the missing computation.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Richstein2001.Gap

namespace LeanLab.Richstein2001

open LeanLab

/-- LEAF. P0017 p. 1747 Section 4: exhaustive search finds a tested partition.
The finite candidate range is inclusive at its lower end and exclusive at its upper end. -/
theorem scan_complete116 (n q : ℕ) (hq : primeB q = true)
    (hnq : primeB (n - q) = true) (hqn : q ≤ n) :
    ∀ fuel start, start ≤ q → q < start + fuel → gbFrom n fuel start = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hs hlt
      omega
  | succ fuel ih =>
      intro start hs hlt
      have hstart : ¬ n < start := by omega
      simp only [gbFrom, ite_eq_right hstart]
      by_cases htest : (primeB start && primeB (n - start)) = true
      · simp only [htest, ite_eq_left]
      · simp only [htest, Bool.false_eq_true, ite_eq_right, not_false_eq_true]
        apply ih (start + 1)
        · by_contra h
          have heq : start = q := by omega
          subst start
          simp [hq, hnq] at htest
        · omega

/-- LEAF. CITED. P0017 p. 1745 abstract and p. 1747 Section 4.
Each verified even number has a partition with smaller prime at most 5569.
This is the missing output of the reported computation. -/
theorem richstein_partitions116 :
    ∀ n, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 14 →
      ∃ q, 2 ≤ q ∧ q ≤ 5569 ∧ q ≤ n ∧ q.Prime ∧ (n - q).Prime := by
  sorry

/-- LEAF. CITED. P0017 p. 1745 abstract and p. 1747 Section 4.
The reported computation supplies a successful scan for every even integer in the range.
No executable or certificate for this full computation is supplied by P0017. -/
theorem richstein_computation116 :
    ∀ n, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 14 → gbFrom n 5568 2 = true := by
  intro n hn h4 hB
  obtain ⟨q, hq2, hqB, hqn, hq, hnq⟩ := richstein_partitions116 n hn h4 hB
  have htest : ∀ r : ℕ, r.Prime → primeB r = true := by
    intro r hr
    simp only [primeB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hr.two_le, primeB_complete_aux r hr⟩
  exact scan_complete116 n q (htest q hq) (htest (n - q) hnq) hqn
    5568 2 hq2 (by omega)

/-- CONDITIONAL ON the full successful-scan computation in P0017 p. 1745.
This assembly uses the existing checker soundness theorem. -/
theorem richstein_of_scan116
    (h : ∀ n, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 14 → gbFrom n 5568 2 = true) :
    EvenGoldbachUpTo (4 * 10 ^ 14) := by
  intro n hn h4 hB
  exact gbFrom_sound n 5568 2 (h n hn h4 hB)

/-- CITED. P0017 p. 1745 abstract. The conclusion is exactly the lab's cited Prop.
The assembly has no sorry. Its computational leaf remains unproved. -/
theorem richstein_decomp116 : EvenGoldbachUpTo (4 * 10 ^ 14) := by
  exact richstein_of_scan116 richstein_computation116

end LeanLab.Richstein2001
