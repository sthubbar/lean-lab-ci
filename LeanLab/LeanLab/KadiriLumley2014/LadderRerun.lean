/-
P0059 arXiv 1407.7902v1 pages 2 and 13, Corollary 1.2 and Table 2.
HP exact base is arXiv 1305.3062 Theorem 4.1.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.BindingRow

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- The rounded base printed in P0059 is below the exact HP endpoint. -/
theorem rounded_hp_le_exact : oddBase ≤ 8875694145621773516800000000000 := by
  norm_num [oddBase]

/-- The named base follows from the precise verification statement.
This theorem is CONDITIONAL ON the cited HP verification. -/
theorem hp_base_of_exact (hHP : TernaryGoldbachUpTo 8875694145621773516800000000000) :
    HelfgottPlattBase := by
  intro n hn h7 hhi
  exact hHP n hn h7 (hhi.trans rounded_hp_le_exact)

/-- All successive row overlaps through row 60 survive the shift by three. -/
theorem tableTwo_shifted_overlap {r s : PrintedRow} (hr : r ∈ tableTwo)
    (hs : s.logIndex ≤ 60) : s.threshold + 3 < (r.gapDenom : ℝ) * evenBase := by
  have hd : (36082898 : ℝ) ≤ r.gapDenom := by
    exact_mod_cast (tableTwo_denominators r hr).1
  have hm : 36082898 * (evenBase : ℝ) ≤ r.gapDenom * evenBase :=
    mul_le_mul_of_nonneg_right hd (by positivity)
  have ht := threshold_le_115e24 hs
  have hnum : (1.15 : ℝ) * 10 ^ 26 + 3 < 36082898 * evenBase := by norm_num [evenBase]
  linarith

/-- The complete printed ladder follows from its own named row inputs.
This is CONDITIONAL ON TableTwoIntervals and the even verification. -/
theorem printed_ladder_of_table (hrows : TableTwoIntervals) (hE : EvenGoldbachUpTo evenBase) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1966196911 * evenBase → IsTernarySum n := by
  have hfirst : KLRow (4 * 10 ^ 18) 36082898 := by
    have h := hrows ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩ (by decide +kernel)
    norm_num [PrintedRow.threshold, evenBase] at h ⊢
    exact h
  have hlast : KLRow (Real.exp 60) 1966196911 := by
    have h := hrows _ row60_mem
    simpa [PrintedRow.threshold] using h
  exact corollary1_2_of hfirst hlast hE

/-- Adding every printed sufficient row range to HP gives exactly HP again.
This is an arithmetic identity of certified ranges, not a Goldbach claim. -/
theorem rerun_range_eq_hp (n : ℕ) :
    (n ≤ oddBase ∨ ∃ r ∈ tableTwo,
      r.threshold + 3 < n ∧ (n : ℝ) < r.gapDenom * evenBase) ↔ n ≤ oddBase := by
  constructor
  · intro h
    rcases h with hbase | ⟨r, hr, hlo, hhi⟩
    · exact hbase
    · by_contra hn
      exact no_table_step_above_hp hr (by omega) hhi
  · exact Or.inl

end LeanLab.KadiriLumley2014.Task64
