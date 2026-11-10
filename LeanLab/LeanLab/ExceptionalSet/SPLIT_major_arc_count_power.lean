/-
Split of `major_arc_count_power` of `LeanLab.ExceptionalSet.SPLIT_theorem51` into three
leaves, all at the same concrete data as the parent: `M = 2x + 1`, `Φ(j) = log p` on the primes
`p ≤ x`, the minor arcs the complement of the major arcs at level `Q = x^{1/10}`, the threshold
`T = M x / 4`, and the window `(x/2, x]`.

* LEAF 1 is the whole count and is where the enlarged arcs `q ≤ x^{1/10}` are paid for: the
  number of even `n` in the window whose major arc part is at most `M x / 4` is below
  `C x / (log x)^A` for every `A > 0`, one constant for all large `x`. That is a log saving,
  strictly weaker than the power saving asked for, and it is the estimate this file assumes.
* LEAF 2 is the first half of turning the log saving into a power saving: `(log x)^4 ≤ x^{1/2}`
  for all large `x`. It is a statement about the real logarithm alone.
* LEAF 3 is the second half: a division inequality, `C x / L^4 ≤ C x^{1/2}` whenever `0 ≤ C`,
  `0 < x` and `L^4 ≤ x^{1/2}`.

The assembly `major_arc_count_power_split` takes the exponent `θ = 1/2`, chains the three, and
has no sorry; it does not use `major_arc_count_power`.

OFF ROUTE, architect 2026-11-10: this split cannot work. LEAF 3 is false, refuted below by
`div_log_saving_le_sqrt_false` at `C = 1`, `x = 4`, `L = 1`. From `L^4 ≤ x^{1/2}` one gets
`C x / L^4 ≥ C x^{1/2}`, the reverse of LEAF 3, so a log saving never yields a power saving
this way. LEAF 1 and LEAF 3 are no longer leaves; provers leave this file alone, and the parent
`major_arc_count_power` needs a power saving from its own source.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_theorem51

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction
open ZMod
open LeanLab.ExceptionalSet.MV

noncomputable section

/-- OFF ROUTE, architect 2026-11-10, was LEAF 1 of 3: the split's LEAF 3 is false, see the header.
The count itself at the enlarged level `Q = x^{1/10}`, with a log saving
instead of a power saving: for every real `A > 0` there are a nonnegative constant `C` and
`X0 ≥ 1` such that for all `x ≥ X0` at most `C x / (log x)^A` of the even `n` in the window
`(x/2, x]` have major arc part of modulus at most `M x / 4`. This is the half where the arcs
`q ≤ x^{1/10}` are paid for, and it is strictly weaker than the power saving of the parent: a
bound `C x^θ` with `θ < 1` implies it, since `(log x)^A ≤ x^{1-θ}` for all large `x`. -/
theorem count_log_saving_enlarged :
    ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X0 : ℕ), 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) / Real.log x ^ A := by
  sorry

/-- LEAF 2 of 3, the log saving against the power `x^{1/2}`: for all large `x` the fourth
power of `log x` is at most `x^{1/2}`. One inequality on the real logarithm, with no counting
in it; it is what allows the exponent `1/2` in the assembly. -/
theorem log_four_le_sqrt :
    ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → Real.log x ^ 4 ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
  -- `(log t)^4 = o(t^(1/2))` at `+∞`: `log = o(t^(1/8))`, and `(1/8) * 4 = 1/2`.
  have hlit : (fun t : ℝ => Real.log t ^ 4) =o[Filter.atTop]
      fun t : ℝ => t ^ ((1 : ℝ) / 2) := by
    have h0 := isLittleO_log_rpow_rpow_atTop (r := ((4 : ℕ) : ℝ)) (s := (1 : ℝ) / 2)
      (by norm_num)
    simpa only [Real.rpow_natCast] using h0
  -- hence eventually `(log t)^4 ≤ t^(1/2)`, by the little-o estimate against itself.
  have hev : ∀ᶠ t : ℝ in Filter.atTop, Real.log t ^ 4 ≤ t ^ ((1 : ℝ) / 2) := by
    filter_upwards [hlit.eventuallyLE, Filter.eventually_gt_atTop (0 : ℝ)] with t ht ht0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_pos (Real.rpow_pos_of_pos ht0 _)] at ht
    exact ht
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  refine ⟨Nat.ceil a, fun x hx => ha (x : ℝ) ?_⟩
  have h1 : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
  have h2 : ((Nat.ceil a : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  linarith

/-- OFF ROUTE, FALSE, architect 2026-11-10, was LEAF 3 of 3, refuted by `div_log_saving_le_sqrt_false`.
The division step that carries the constant through: if `C ≥ 0`, `x > 0` and
`L^4 ≤ x^{1/2}`, then `C x / L^4 ≤ C x^{1/2}`. The hypothesis `L^4 ≤ x^{1/2}` already forces
`L ≠ 0`, so `L = 0` is not a case of this leaf; `x = 1` is, with `L^4 = 1`, and there the two
sides agree. -/
theorem div_log_saving_le_sqrt :
    ∀ C x L : ℝ, 0 ≤ C → 0 < x → L ^ 4 ≤ x ^ ((1 : ℝ) / 2) →
      C * x / L ^ 4 ≤ C * x ^ ((1 : ℝ) / 2) := by
  sorry

/-- `major_arc_count_power` assembled from the three leaves at `θ = 1/2`: the count is below
`C x / (log x)^4` by LEAF 1, `(log x)^4 ≤ x^{1/2}` by LEAF 2, and the division of LEAF 3
turns the first into `C x^{1/2}`. -/
theorem major_arc_count_power_split :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  obtain ⟨C₁, X₁, hC₁, hX₁, h₁⟩ := count_log_saving_enlarged ((4 : ℕ) : ℝ) (by norm_num)
  obtain ⟨X₂, h₂⟩ := log_four_le_sqrt
  refine ⟨(1 : ℝ) / 2, C₁, max (max X₁ X₂) 3, by norm_num, by norm_num, hC₁,
    le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro x hx
  have hx1 : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    linarith
  have hb := h₁ x hx1
  rw [Real.rpow_natCast] at hb
  have hlog := div_log_saving_le_sqrt C₁ (x : ℝ) (Real.log x) hC₁ hxpos (h₂ x hx2)
  exact le_trans hb hlog

/-- LEAF 3 is false: at `C = 1`, `x = 4`, `L = 1` its hypotheses hold, `1 ≤ 4^{1/2} = 2`, and
its conclusion reads `4 ≤ 2`. The true direction is `C x^{1/2} ≤ C x / L^4` when `0 < L`. -/
theorem div_log_saving_le_sqrt_false :
    ¬ (∀ C x L : ℝ, 0 ≤ C → 0 < x → L ^ 4 ≤ x ^ ((1 : ℝ) / 2) →
      C * x / L ^ 4 ≤ C * x ^ ((1 : ℝ) / 2)) := by
  intro h
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hc := h 1 4 1 (by norm_num) (by norm_num) (by rw [h4]; norm_num)
  rw [h4] at hc
  norm_num at hc

#print axioms div_log_saving_le_sqrt_false

-- Axiom audit driver for the assembly.
#print axioms major_arc_count_power_split

end

end LeanLab.ExceptionalSet.BG2026
