/-
P0044, Cai 2002. Wiring of the Theorem on pages 597 to 598 through the
supply assemblies of task337.
AI wrote the Lean code. Binary Goldbach is open.
The sealed leaves leaf118_sieve_one, leaf118_sieve_two and leaf118_sieve_three
are not edited; this module only re-assembles the same MainTheorem downstream,
with the three upper sieve leaves replaced by sieve_one_supply337,
sieve_two_supply337 and sieve_three_supply337. Those are CONDITIONAL on
leaf337_one_sieve, leaf337_two_switching and leaf337_three_switching.
The lower sieve stays CONDITIONAL on the cited leaf306_theorem6.
-/
import LeanLab.Cai2002.Decomp337c

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- The exact cited MainTheorem, assembled as in main_theorem_decomp118 on Cai
page 604, but with displays 4.7, 4.14 and 4.15 supplied by the task337 supply
assemblies. CONDITIONAL on leaf306_theorem6, leaf337_one_sieve,
leaf337_two_switching and leaf337_three_switching. -/
theorem main_theorem_wire337 : MainTheorem := by
  obtain ⟨n0, h0⟩ := leaf118_loss
  obtain ⟨n1, h1⟩ := leaf118_sieve_lower
  obtain ⟨n2, h2⟩ := sieve_one_supply337
  obtain ⟨n3, h3⟩ := sieve_two_supply337
  obtain ⟨n4, h4⟩ := sieve_three_supply337
  refine ⟨max 177147 (max n0 (max n1 (max n2 (max n3 n4)))), ?_⟩
  intro N he hN
  have hcut : 177147 ≤ N := (le_max_left ..).trans hN
  have hrest := (le_max_right ..).trans hN
  have hn0 : n0 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn1 : n1 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn2 : n2 ≤ N := (le_max_left ..).trans hrest
  have hrest := (le_max_right ..).trans hrest
  have hn3 : n3 ≤ N := (le_max_left ..).trans hrest
  have hn4 : n4 ≤ N := (le_max_right ..).trans hrest
  have hp := leaf118_scale_pos N (by omega)
  have hw := leaf118_weighted N hcut
  have hl := h0 N hn0
  have hs := h1 N he hn1
  have hs1 := h2 N he hn2
  have hs2 := h3 N he hn3
  have hs3 := h4 N he hn4
  have htarget :
      0.01 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) < (S N 0.95 : ℝ) := by
    linarith
  simpa only [mul_div_assoc, mul_assoc] using htarget

#print axioms main_theorem_wire337

end LeanLab.Cai2002
