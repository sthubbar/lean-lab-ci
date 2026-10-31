/-
P0042 Table 3 on page 429 and P0005 Table 4 on page 2043.
The certified record rows force lower bounds on uniform partition bounds.
Full-range upper bounds remain named cited inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Verifications.CitedInputs
import LeanLab.Verifications.Top50.Records2

namespace LeanLab.Verifications.TableBoundsTask72

open CitedInputs

/-- P0042 Table 3: its last record lies inside the paper's verification range. -/
theorem p0042_record_instance :
    Even (12703943222 : ℕ) ∧ 4 ≤ (12703943222 : ℕ) ∧
    (12703943222 : ℕ) ≤ 2 * 10 ^ 10 ∧ minGB 12703943222 = 2029 := by
  refine ⟨by norm_num, by norm_num, by norm_num, Top50.Records2.minGB_2029⟩

/-- The P0042 record prevents every smaller uniform bound on that same range. -/
theorem p0042_bound_ge_2029 {b : ℕ}
    (h : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 10 ^ 10 → minGB n ≤ b) :
    2029 ≤ b := by
  have hr := p0042_record_instance
  have hb := h 12703943222 hr.1 hr.2.1 hr.2.2.1
  rwa [hr.2.2.2] at hb

/-- CONDITIONAL on the cited P0042 bound. Its exact maximum is 2029. -/
theorem p0042_max_attained_of (h : P0042MinimalBound) :
    (∀ n : ℕ, Even n → 4 ≤ n → n ≤ 2 * 10 ^ 10 → minGB n ≤ 2029) ∧
    (Even (12703943222 : ℕ) ∧ 4 ≤ (12703943222 : ℕ) ∧
      (12703943222 : ℕ) ≤ 2 * 10 ^ 10 ∧ minGB 12703943222 = 2029) :=
  ⟨h, p0042_record_instance⟩

/-- The P0005 record prevents every smaller uniform bound on that same range. -/
theorem p0005_bound_ge_9781 {b : ℕ}
    (h : ∀ n : ℕ, Even n → 4 ≤ n → n ≤ 4 * 10 ^ 18 → minGB n ≤ b) :
    9781 ≤ b := by
  have hb := h OeSHP.nRec (by norm_num [OeSHP.nRec])
    (by norm_num [OeSHP.nRec]) (by norm_num [OeSHP.nRec])
  rwa [OeSHP.minGB_nRec] at hb

/-- At the P0005 record gap any uniform gap bound is at least 1476. -/
theorem p0005_gap_bound_ge_1476 {b : ℕ}
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p < q → q ≤ 4 * 10 ^ 18 →
      (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ b) : 1476 ≤ b := by
  have hi : ∀ r, OeSHP.pGap < r → r < OeSHP.pGap + 1476 → ¬ r.Prime := by
    intro r hlo hhi
    have hc := OeSHP.gap_composite (r - OeSHP.pGap) (by omega) (by omega)
    simpa only [Nat.add_sub_of_le hlo.le] using hc
  have hb := h OeSHP.pGap (OeSHP.pGap + 1476) OeSHP.pGap_prime.1
    OeSHP.pGap_prime.2 (by omega) (by norm_num [OeSHP.pGap]) hi
  simpa only [Nat.add_sub_cancel_left] using hb

end LeanLab.Verifications.TableBoundsTask72
