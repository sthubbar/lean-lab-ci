/-
U-6818, P0005 Oliveira e Silva, Herzog, Pardi 2014: cross-table consistency of the printed
record tables, zero sorry, by the kernel over every pair of rows.
Table 4 lists the records of p(n), Table 5 the records of S(p), the least n with p(n) = p.
A record row (n, p) of Table 4 has n = S(p), because every m < n has p(m) < p. Hence, for
any row (q, S) of Table 5: q = p forces S = n, and q > p forces S > n, since S(q) is then
the least m with p(m) = q > p, and every m ≤ n has p(m) ≤ p.
Table 8 lists maximal gaps (p, g), Table 9 record first occurrences (g', P(g')). A maximal
gap g at p is the first gap of size g, and every gap starting below p is smaller than g.
Hence g' = g forces P(g') = p, and g' > g forces P(g') > p.
These are necessary conditions on the printed numbers, so a misprinted row could fail them;
all 68 · 131 and 75 · 127 pairs pass. They do NOT prove that any row is a record; that
stays the authors' computation, cited.
AI-written Lean code, Claude, 2026-10-21, run 20261021T0316Z-cloud57. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.OeSHP2014.Tables
import LeanLab.OeSHP2014.Table9
import LeanLab.Verifications.Top50.GapsSummary

namespace LeanLab.OeSHP2014

/-- Tables 4 and 5 agree: a shared p has the same n, and a later p in Table 5 has larger S. -/
theorem table4_table5_joint : ∀ x ∈ table4, ∀ y ∈ table5,
    (y.1 = x.2 → y.2 = x.1) ∧ (x.2 < y.1 → x.1 < y.2) := by
  have h : table4.all (fun x => table5.all (fun y =>
      (y.1 != x.2 || y.2 == x.1) && (!(decide (x.2 < y.1)) || decide (x.1 < y.2)))) = true := by
    decide +kernel
  intro x hx y hy
  have := List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨fun e => h1.resolve_left (not_not.mpr e), fun l => h2.resolve_left (not_not.mpr l)⟩

/-- Tables 8 and 9 agree: a shared g has the same prime, and a larger g in Table 9 starts later. -/
theorem table8_table9_joint : ∀ x ∈ LeanLab.Verifications.Top50.Gaps.gapTable, ∀ y ∈ table9,
    (y.1 = x.2 → y.2 = x.1) ∧ (x.2 < y.1 → x.1 < y.2) := by
  have h : LeanLab.Verifications.Top50.Gaps.gapTable.all (fun x => table9.all (fun y =>
      (y.1 != x.2 || y.2 == x.1) && (!(decide (x.2 < y.1)) || decide (x.1 < y.2)))) = true := by
    decide +kernel
  intro x hx y hy
  have := List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨fun e => h1.resolve_left (not_not.mpr e), fun l => h2.resolve_left (not_not.mpr l)⟩

end LeanLab.OeSHP2014

#print axioms LeanLab.OeSHP2014.table4_table5_joint
#print axioms LeanLab.OeSHP2014.table8_table9_joint
