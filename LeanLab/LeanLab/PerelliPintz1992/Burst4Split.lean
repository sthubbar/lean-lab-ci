/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 4, 2026-11-12. The Theorem, p. 356, `perelliPintz` in Statements.lean,
split into the paper's own top-level structure:

* Section 2, displays 4 and 5, pp. 357 to 359: the reduction of the Theorem to 6 and 7.
  PROVED earlier, reused: `MainAssembly.mainTheorem_of_wide`.
* Section 4, displays 8 to 20, pp. 359 to 362: the major arcs estimate 6. LEAF, sorry,
  `major_arcs_estimate6` below.
* Section 5, displays 22 to 27, pp. 363 and 364: the Farey and Gallagher reduction of 7 to the
  character expression. LEAF, sorry, `reduction27A_wide` below, every real centre.
* Sections 5 and 6, pp. 365 to 372: every logarithmic saving for the character expression.
  LEAF, sorry, reused unchanged: `Decomp1624.energy_decayA`.
* Glue, PROVED here: the character expression at any real centre is bounded by its value at the
  centre clamped to [0, 1], `energyA_le_clamp`; hence `estimate7Wide_of_split`.

`perelliPintz_of_split` has the type `MainTheorem` of `perelliPintz` and no sorry of its own.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
/-
Status CODEX task544, 2026-11-14. The two original estimate statements and their
assemblies moved to Decomp544 with identical names and statement text.
The clamping definitions and their proved comparisons remain here.
Import Decomp544 to use the moved reduction and assembly declarations.
-/
import LeanLab.PerelliPintz1992.MainAssembly
import LeanLab.PerelliPintz1992.Decomp1624

namespace LeanLab.PerelliPintz1992.Burst4Split
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ### The retained clamping data -/

/-! ### Glue, proved -/

/-- The centre ξ clamped to [0, 1]. -/
def clamp01 (ξ : ℝ) : ℝ := max 0 (min ξ 1)

attribute [-instance] Finset.decidableExistsAndFinsetCoe Finset.decidableExistsAndFinset in
/-- The Farey modulus family of p. 363 at a real centre is contained in the family at the
clamped centre. Every arc `a/q` has `1 ≤ a ≤ q`, so it lies in [0, 1]. PROVED. -/
theorem Y_subset_clamp {N : ℕ} (hN : 1 ≤ N) (ε ξ : ℝ) (M : ℕ) :
    Y N ε ξ M ⊆ Y N ε (clamp01 ξ) M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : 0 < 1 / H N ε := one_div_pos.mpr (Real.rpow_pos_of_pos hNp _)
  intro q hq
  obtain ⟨hb, hM, hM', a, ha, hc, α, hα, hx⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hb, hM, hM', a, ha, hc, ?_⟩
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have haq : (a : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp ha).2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.pos
  have haq0 : 0 < (a : ℝ) / q := div_pos (by linarith) hq0
  have haq1 : (a : ℝ) / q ≤ 1 := (div_le_one hq0).mpr haq
  rcases le_or_gt ξ 0 with h0 | h0
  · have hcl : clamp01 ξ = 0 := by
      unfold clamp01; rw [min_eq_left (by linarith)]; exact max_eq_left h0
    rw [hcl]
    rcases le_or_gt 0 α with hα0 | hα0
    · refine ⟨α, hα, ?_⟩
      rw [sub_zero, abs_of_nonneg hα0]
      have := (abs_lt.mp hx).2
      linarith
    · refine ⟨0, ?_, by simpa using hH⟩
      have h1 := (abs_le.mp hα).1
      rw [zero_sub, abs_neg, abs_of_pos haq0]
      linarith
  rcases le_or_gt ξ 1 with h1 | h1
  · have hcl : clamp01 ξ = ξ := by
      unfold clamp01; rw [min_eq_left h1]; exact max_eq_right h0.le
    rw [hcl]; exact ⟨α, hα, hx⟩
  · have hcl : clamp01 ξ = 1 := by
      unfold clamp01; rw [min_eq_right h1.le]; exact max_eq_right zero_le_one
    rw [hcl]
    rcases le_or_gt α 1 with hα1 | hα1
    · refine ⟨α, hα, ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have := (abs_lt.mp hx).1
      linarith
    · refine ⟨1, ?_, by simpa using hH⟩
      have h2 := (abs_le.mp hα).2
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- The character expression at a real centre is at most its value at the clamped centre.
PROVED. -/
theorem energyA_le_clamp {N : ℕ} (hN : 1 ≤ N) (ε ξ : ℝ) (M : ℕ) :
    energyA N ε ξ M ≤ energyA N ε (clamp01 ξ) M := by
  unfold energyA
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Y_subset_clamp hN ε ξ M)
    (fun q _ _ => sq_nonneg _)

example : MainTheorem := perelliPintz

#print axioms Y_subset_clamp
#print axioms energyA_le_clamp

end
end LeanLab.PerelliPintz1992.Burst4Split
