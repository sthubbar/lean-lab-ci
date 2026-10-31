import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! Internal arithmetic of Table 11 on page 2056.
AI wrote the Lean code. Binary Goldbach is OPEN.
These are checks of printed integers, not enumerations of twin primes.
-/
namespace LeanLab.OeSHP2014.Task74

/-- The 21 printed cutoff and count pairs, in increasing cutoff order. -/
def twinRows : List (ℕ × ℕ) := [
  (1000000000000, 1870585220),
  (2000000000000, 3552770943),
  (4000000000000, 6756832076),
  (10000000000000, 15834664872),
  (20000000000000, 30198862775),
  (40000000000000, 57657248284),
  (100000000000000, 135780321665),
  (200000000000000, 259858400254),
  (400000000000000, 497794845572),
  (1000000000000000, 1177209242304),
  (2000000000000000, 2259758303674),
  (4000000000000000, 4341401630211),
  (10000000000000000, 10304195697298),
  (20000000000000000, 19831847025792),
  (40000000000000000, 38196843833352),
  (100000000000000000, 90948839353159),
  (200000000000000000, 175448328823978),
  (400000000000000000, 338672552419828),
  (1000000000000000000, 808675888577436),
  (2000000000000000000, 1563203499075902),
  (4000000000000000000, 3023463123235320)]

/-- Counts in the 20 successive intervals, derived by subtraction. -/
def twinIncrements : List ℕ := [1682185723, 3204061133, 9077832796, 14364197903, 27458385509, 78123073381, 124078078589, 237936445318, 679414396732, 1082549061370, 2081643326537, 5962794067087, 9527651328494, 18364996807560, 52751995519807, 84499489470819, 163224223595850, 470003336157608, 754527610498466, 1460259624159418]

/-- Every printed pair obeys count monotonicity and the elementary interval capacity. -/
theorem table11_pairwise : ∀ a ∈ twinRows, ∀ b ∈ twinRows,
    a.1 ≤ b.1 → a.2 ≤ b.2 ∧ b.2 - a.2 ≤ (b.1 - a.1) / 2 := by
  norm_num [twinRows]

/-- Every printed count is reconstructed by summing successive interval counts. -/
theorem table11_prefix_sums :
    twinIncrements.scanl (· + ·) 1870585220 = twinRows.map Prod.snd := by
  norm_num [twinIncrements, twinRows, List.scanl]

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.table11_pairwise

#print axioms LeanLab.OeSHP2014.Task74.table11_prefix_sums
