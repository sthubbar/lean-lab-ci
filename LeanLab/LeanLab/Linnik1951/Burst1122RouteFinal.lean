/-
Burst 1122 final route assembly for P0093, Linnik 1951. Burst 2026-11-22, session S3,
step route_final1122.

This file stacks the two branches of the burst. Burst1122RouteWiring proves
linnik1951_decomposed_of_transfer_b1122 from GRH and one hypothesis hT, the statement of
grh_mellin_transfer519. Burst1122GrhTransfer519 proves that exact statement as
grh_mellin_transfer519_b1122, conditional on three classed LEAFs of its own. Here hT is
instantiated with grh_mellin_transfer519_b1122 hG, so the old sorry carrier
Task519.grh_mellin_transfer519 leaves the route. A closure walk, now in build/CLOUD-burst1122-S66-closure.log, follows the closure
and prints every LeanLab declaration that carries a sorry itself. No definition and no
sorry in this file.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Burst1122RouteWiring
import LeanLab.Linnik1951.Burst1122GrhTransfer519

namespace LeanLab.Linnik1951

open LeanLab.Linnik LeanLab.DERZ1997

/-- P0093 pages 154 and 168 to 169, with page 159 before equation 5.1. The exact
statement of linnik1951_decomposed111 in Decomp111. Proof: the route of
linnik1951_decomposed_of_transfer_b1122 with hT instantiated by
Task519.grh_mellin_transfer519_b1122 hG. The three former LEAFs of Burst1122GrhTransfer519,
grh_strip_log_bound_b1122, cahen_mellin_line_two_b1122 and mellin_line_shift_b1122, are PROVED on
claude/Linnik1951-grh_mellin_transfer519-r2-p2, so on claude/Linnik1951-integrate1122 this
theorem depends on GRH only; build/CLOUD-burst1122-S66-closure.log has the closure walk. -/
theorem linnik1951_decomposed_final_b1122 : GRH → ∃ K, AllLargeEven (LinnikAtMost K) :=
  fun hG => linnik1951_decomposed_of_transfer_b1122 hG (Task519.grh_mellin_transfer519_b1122 hG)

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.linnik1951_decomposed_final_b1122

/-! The closure walk that used to run here as a run_cmd was moved out of the source on
branch claude/Linnik1951-integrate1122, burst session S66, because the seal gate bans
metaprograms. The same walk, word for word, and its output are in
build/CLOUD-burst1122-S66-closure.log. -/
