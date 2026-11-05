import Mathlib

/-!
# Saouter 1998, Audit1620: two false claims of a novelty report

AI wrote this Lean code, unit U-1620, run 20261105T0803Z-23816. Binary Goldbach is OPEN.
Both refutations are of research/novelty/Saouter1998-deepseek-20261104T1237Z.md, not of the paper and
not of any lab statement. The report's section 6 item 3 says every odd `c ≡ 1 mod 2^22` makes
`5·2^23 k + c ≡ 3 mod 10`. Its section 6 item 2 and ranked finding 3 say a ladder of about 25 rungs with
gaps below 4e18 reaches 8.875e30. The lab's 25 rungs in ProthLadder1597 reach 1e20, and that is the limit.
-/

namespace LeanLab.Saouter1998.Audit1620

/-- REFUTATION of the report's offset independence, item 3, at `c = 1`, `k = 0`. -/
theorem report_offset_false :
    ¬ ∀ c : ℕ, c % 2 ^ 22 = 1 → Odd c → ∀ k : ℕ, (5 * 2 ^ 23 * k + c) % 10 = 3 := by
  intro h
  have := h 1 (by norm_num) (by decide) 0
  norm_num at this

/-- The true form: the last digit of a rung is the last digit of the offset, so item 3 needs
`c ≡ 3 mod 10` as a hypothesis. -/
theorem rung_mod_ten (c k : ℕ) : (5 * 2 ^ 23 * k + c) % 10 = c % 10 := by
  omega

/-- A list of rungs starting below `E` with gaps below `E` stays below `(n + 1) E`. -/
theorem rung_le {E : ℕ} {f : ℕ → ℕ} (h0 : f 0 ≤ E) (h : ∀ i, f (i + 1) ≤ f i + E) (n : ℕ) :
    f n ≤ (n + 1) * E := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have := h n
    nlinarith

/-- REFUTATION of the report's 25 rung ladder to 8.875e30, item 2: with `p₀ ≤ 4e18` and 24 gaps
at most 4e18, `p₂₄ + 4e18` is at most 1.04e20, so it cannot reach the printed 8.875e30 range. -/
theorem report_ladder_false {f : ℕ → ℕ} (h0 : f 0 ≤ 4 * 10 ^ 18)
    (h : ∀ i, f (i + 1) ≤ f i + 4 * 10 ^ 18) :
    f 24 + 4 * 10 ^ 18 < 8875694145621773516800000000000 := by
  have := rung_le h0 h 24
  omega

end LeanLab.Saouter1998.Audit1620

#print axioms LeanLab.Saouter1998.Audit1620.report_offset_false
#print axioms LeanLab.Saouter1998.Audit1620.rung_mod_ten
#print axioms LeanLab.Saouter1998.Audit1620.report_ladder_false
