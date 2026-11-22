/-
Prep1121 route wiring audit for P0093, Linnik 1951. Burst prep 2026-11-21, step L51-wiring.

#print axioms only says that sorryAx occurs in the closure of
linnik1951_decomposed_prep1121. The closure walk, now in build/CLOUD-burst1122-S66-closure.log, names the declarations that carry a
sorry themselves: it walks the constants used by that theorem inside the LeanLab
namespace and prints every one whose type or value mentions sorryAx directly. Those are
the open leaves the route still needs. No theorem, no definition and no sorry here.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Prep1121RouteWiring

#print axioms LeanLab.Linnik1951.linnik1951_decomposed_prep1121

/-! The closure walk that used to run here as a run_cmd was moved out of the source on
branch claude/Linnik1951-integrate1122, burst session S66, because the seal gate bans
metaprograms. The same walk, word for word, and its output are in
build/CLOUD-burst1122-S66-closure.log. -/
