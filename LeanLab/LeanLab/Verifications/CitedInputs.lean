/-
Exact cited verification inputs for the remaining computations.
P0005 DOI https://doi.org/10.1090/S0025-5718-2013-02787-1
P0042 source https://ir.cwi.nl/pub/1570/
These definitions assert no computation. Results using them are CONDITIONAL.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.OeSHPTables

namespace LeanLab.Verifications.CitedInputs

open LeanLab.SchnirelmannConstant LeanLab.Tao2012

/-- P0005 abstract, page 2033. -/
def P0005Even : Prop := EvenGoldbachUpTo (4 * 10 ^ 18)

/-- P0006 abstract, page 1, arXiv https://arxiv.org/abs/1305.3062. -/
def P0006Ternary : Prop := TernaryGoldbachUpTo 8875694145621773516800000000000

/-- P0017 title, even Goldbach to four times ten to the fourteenth. -/
def P0017Even : Prop := EvenGoldbachUpTo (4 * 10 ^ 14)

/-- P0037 verification range, even Goldbach to ten to the fourteenth. -/
def P0037Even : Prop := EvenGoldbachUpTo (10 ^ 14)

/-- P0041 title, even Goldbach to four times ten to the eleventh. -/
def P0041Even : Prop := EvenGoldbachUpTo (4 * 10 ^ 11)

/-- P0018 title, odd Goldbach to ten to the twentieth. -/
def P0018Ternary : Prop := TernaryGoldbachUpTo (10 ^ 20)

/-- P0005 Table 4, page 2043, upper bound only. -/
def P0005MinimalBound : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 18 → minGB n ≤ 9781

/-- P0005 Table 8, page 2050, upper bound only. -/
def P0005GapBound : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
    (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ 1476

/-- P0042 Table 3, page 429, and the upper bound on page 428. -/
def P0042MinimalBound : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 10 ^ 10 → minGB n ≤ 2029

/-- P0042 page 432 ratio claim, with the paper's odd-prime convention starting at six. -/
def P0042RatioBound : Prop :=
  ∀ n : ℕ, Even n → 6 ≤ n → n ≤ 2 * 10 ^ 10 →
    (minGB n : ℝ) < 1.603 * Real.log n ^ 2 * Real.log (Real.log n)

/-- The least-prime bound is equivalent to a bounded witness when a partition exists. -/
theorem minGB_le_iff_of_exists {n b : ℕ}
    (hex : ∃ p, p.Prime ∧ (n - p).Prime) :
    minGB n ≤ b ↔ ∃ p, p ≤ b ∧ p.Prime ∧ (n - p).Prime := by
  unfold minGB
  rw [dif_pos hex]
  constructor
  · intro h
    exact ⟨Nat.find hex, h, Nat.find_spec hex⟩
  · rintro ⟨p, hp, hpp⟩
    exact (Nat.find_min' hex hpp).trans hp

/-- A concrete partition witnesses the hypotheses of the least-prime equivalence. -/
theorem minGB_le_iff_instance :
    (∃ p : ℕ, p.Prime ∧ (4 - p).Prime) ∧ minGB 4 ≤ 2 := by
  have hex : ∃ p : ℕ, p.Prime ∧ (4 - p).Prime := ⟨2, by norm_num⟩
  exact ⟨hex, (minGB_le_iff_of_exists hex).mpr ⟨2, le_rfl, by norm_num⟩⟩

/-- CONDITIONAL on the full-range P0005 bound. The maximum is attained. -/
theorem p0005_minimum_max_of (h : P0005MinimalBound) :
    (∀ n : ℕ, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 18 → minGB n ≤ 9781) ∧
    (Even OeSHP.nRec ∧ 4 ≤ OeSHP.nRec ∧ OeSHP.nRec ≤ 4 * 10 ^ 18 ∧
      minGB OeSHP.nRec = 9781) := by
  refine ⟨h, ?_, ?_, ?_, OeSHP.minGB_nRec⟩ <;> norm_num [OeSHP.nRec]

/-- CONDITIONAL on the full-range P0005 gap bound. The maximum is attained. -/
theorem p0005_gap_max_of (h : P0005GapBound) :
    P0005GapBound ∧
    (OeSHP.pGap.Prime ∧ (OeSHP.pGap + 1476).Prime ∧
      OeSHP.pGap < OeSHP.pGap + 1476 ∧ OeSHP.pGap + 1476 ≤ 4 * 10 ^ 18 ∧
      (∀ r, OeSHP.pGap < r → r < OeSHP.pGap + 1476 → ¬ r.Prime) ∧
      OeSHP.pGap + 1476 - OeSHP.pGap = 1476) := by
  refine ⟨h, OeSHP.pGap_prime.1, OeSHP.pGap_prime.2, by omega,
    by norm_num [OeSHP.pGap], ?_, by omega⟩
  intro r hlo hhi
  have hc := OeSHP.gap_composite (r - OeSHP.pGap) (by omega) (by omega)
  simpa only [Nat.add_sub_of_le hlo.le] using hc

end LeanLab.Verifications.CitedInputs
