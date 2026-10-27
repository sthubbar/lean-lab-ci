/-
P0037, unit U-0938, run 20261018T1002Z-987. Splitting a Lucas certificate chain into pieces,
so each piece is its own kernel check.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.DtRS1998.BigCert

namespace LeanLab.DtRS1998.Big

theorem chainB_append : ∀ (known : List ℕ) (A B : List Cert),
    chainB known (A ++ B) = (chainB known A && chainB ((A.map Prod.fst).reverse ++ known) B) := by
  intro known A
  induction A generalizing known with
  | nil => intro B; simp [chainB]
  | cons c t ih =>
    intro B
    simp only [List.cons_append, chainB, ih, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Bool.and_assoc, List.nil_append]

end LeanLab.DtRS1998.Big
