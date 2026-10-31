/-
AI wrote this Lean code for CODEX task128.
P0073, Note added in proof, page 433.
The paper reports a sieve verification, not a written analytic proof.
The coverage leaves retain existing cited inputs. Goldbach is open.
-/
import LeanLab.SteinStein1965.Statements

namespace LeanLab.SteinStein1965

/-- CITED. The verification through one hundred million reported on page 433. -/
def Goldbach1e8Claim : Prop := EvenGoldbachUpTo (10 ^ 8)

/-- LEAF. Page 433, lower coverage from the earlier verification on page 429.
CONDITIONAL ON goldbach_1e7_cited. -/
theorem decomp128_low : EvenGoldbachUpTo 63275 := by
  intro N hEven hLo hHi
  exact goldbach_1e7_cited N hEven hLo (by omega)

/-- LEAF. Page 433, the stated square bound supplies upper coverage.
CONDITIONAL ON noteP_cited. -/
theorem decomp128_high (N : ℕ) (hEven : N % 2 = 0)
    (hLo : 63276 ≤ N) (hHi : N ≤ 10 ^ 8) :
    ∃ q, IsLeastGoldbachPrime N q ∧ q * q < N := by
  exact noteP_cited N hEven hLo hHi

/-- LEAF. Page 433, a square-bounded least pair is a Goldbach representation. -/
theorem decomp128_pair (N q : ℕ) (hPair : IsLeastGoldbachPrime N q)
    (hSquare : q * q < N) : IsGoldbachSum N := by
  have hq : q ≤ N := by nlinarith [hPair.1]
  exact ⟨q, N - q, hPair.2.1, hPair.2.2.1, Nat.add_sub_of_le hq⟩

/-- Page 433, coverage assembly with both empirical inputs explicit.
CONDITIONAL ON the lower verification and the upper least-pair assertion. -/
theorem decomp128_of
    (hLow : EvenGoldbachUpTo 63275)
    (hHigh : ∀ N, N % 2 = 0 → 63276 ≤ N → N ≤ 10 ^ 8 →
      ∃ q, IsLeastGoldbachPrime N q ∧ q * q < N) : Goldbach1e8Claim := by
  intro N hEven hLo hHi
  by_cases hSmall : N ≤ 63275
  · exact hLow N hEven hLo hSmall
  · obtain ⟨q, hPair, hSquare⟩ := hHigh N (Nat.even_iff.mp hEven) (by omega) hHi
    exact decomp128_pair N q hPair hSquare

/-- CITED. Page 433. The exact stated Prop assembled from the leaves.
CONDITIONAL ON goldbach_1e7_cited and noteP_cited. -/
theorem goldbach_1e8_cited : Goldbach1e8Claim := by
  exact decomp128_of decomp128_low decomp128_high

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.decomp128_low
#print axioms LeanLab.SteinStein1965.decomp128_high
#print axioms LeanLab.SteinStein1965.decomp128_pair
#print axioms LeanLab.SteinStein1965.decomp128_of
#print axioms LeanLab.SteinStein1965.goldbach_1e8_cited
