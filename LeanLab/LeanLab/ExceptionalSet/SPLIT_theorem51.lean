/-
Split of `theorem51` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026` into two leaves.

`theorem51` asserts `PowerSaving`, that is `E X ≤ C X^{1-δ}` for one `δ > 0`. The lab's circle
method frame reduces it to two analytic inputs on the concrete data of the power saving route:
`M = 2x + 1`, `Φ(j) = log p` on the primes `p ≤ x`, the minor arcs the complement of the major
arcs at level `Q = x^{1/10}`, and the level `T = M x / 4`.

* LEAF 1, the counting half: the even `n` in the window `(x/2, x]` whose major arc part has
  modulus at most `T` number at most `C x^θ` with `θ < 1`. This is where the enlarged arcs
  `q ≤ x^{1/10}` are paid for, by the large sieve and a zero density bound.
* LEAF 2, the mean value half: `M` times the fourth moment of the exponential sum over the
  minor arcs, divided by `T²`, is at most `C x^θ` with `θ < 1`.

`bad_le_skeleton` covers the exceptional evens of the window by those two counts, and
`powerBound_of_window` sums the window bound over the dyadic halvings to `E`. Both are proved
in the modules imported below, so the assembly carries no input of its own beyond the leaves.
Neither leaf alone gives `PowerSaving`: the skeleton needs the two together.

Every leaf is OPEN. The assembly `theorem51_split` has no sorry and does not use `theorem51`.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.BhowmikGrimmelt2026
import LeanLab.ExceptionalSet.MVConditional
import LeanLab.ExceptionalSet.MVEstermann

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction
open ZMod
open LeanLab.ExceptionalSet.MV

noncomputable section

/-- LEAF 1 of 2, the counting half of the split: on the concrete data of the power saving
route, some `θ < 1` bounds the number of even `n` in the window `(x/2, x]` whose major arc
part has modulus at most `M x / 4`, the level that the major arc asymptotic clears. The
constant is one nonnegative `C` for all `x ≥ X0`, and `X0 ≥ 1` so that the window and the
level are nondegenerate. Only this count is asserted; no bound on the minor arcs. -/
theorem major_arc_count_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
              ‖majorPart (logPrimes x) (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)))
                (n : ZMod (Mx x))‖ ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ)
          ≤ C * (x : ℝ) ^ θ := by
  sorry

/-- LEAF 2 of 2, the mean value half of the split: on the same data, `M` times the fourth
moment `∑ ‖𝓕 Φ k‖⁴` over the minor arcs, divided by `T² = (M x / 4)²`, is at most `C x^θ` with
`θ < 1`. The moment is the quantity `card_large_minor_le` converts into a count of bad `n`, so
this half and LEAF 1 together cover the window. Only this moment is asserted; no count of
exceptional `n`. -/
theorem minor_arc_l4_power :
    ∃ (θ C : ℝ) (X0 : ℕ), 0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧ 1 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (Mx x : ℝ) * (∑ k ∈ minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10)), ‖𝓕 (logPrimes x) k‖ ^ 4)
            / ((Mx x : ℝ) * x / 4) ^ 2 ≤ C * (x : ℝ) ^ θ := by
  sorry

/-- `theorem51` of `LeanLab.ExceptionalSet.BhowmikGrimmelt2026`, assembled from the two leaves
at the level `Q = x^{1/10}`: the window bound at the larger of the two exponents, then the
dyadic summation to `E`. -/
theorem theorem51_split : PowerSaving := by
  obtain ⟨θ₁, C₁, X₁, hθ₁0, hθ₁1, hC₁, hX₁, h1⟩ := major_arc_count_power
  obtain ⟨θ₂, C₂, X₂, hθ₂0, hθ₂1, hC₂, hX₂, h2⟩ := minor_arc_l4_power
  have hθ0 : 0 < max θ₁ θ₂ := lt_of_lt_of_le hθ₁0 (le_max_left _ _)
  have hθ1 : max θ₁ θ₂ < 1 := max_lt hθ₁1 hθ₂1
  refine ⟨1 - max θ₁ θ₂, by linarith, ?_⟩
  rw [sub_sub_cancel]
  refine powerBound_of_window (θ := max θ₁ θ₂) (C := C₁ + C₂) (X0 := max X₁ X₂) hθ0 ?_
  intro x hx
  have hb1 := h1 x (le_trans (le_max_left _ _) hx)
  have hb2 := h2 x (le_trans (le_max_right _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_trans hX₁ (le_max_left _ _)) hx
  have hxM : 2 * x < Mx x := by unfold Mx; omega
  have hMpos : (0 : ℝ) < (Mx x : ℝ) := by
    have : 0 < Mx x := by unfold Mx; omega
    exact_mod_cast this
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hT : (0 : ℝ) < (Mx x : ℝ) * x / 4 := by
    have := mul_pos hMpos hxpos
    linarith
  have hΦ : PrimeSupported (logPrimes x) x := by
    intro j hj
    by_contra hcon
    exact hj (by simp [logPrimes, hcon])
  have hsk := bad_le_skeleton (M := Mx x) (Φ := logPrimes x) (x := x) (a := x / 2 + 1) hΦ hxM
    (minorArcs x ((x : ℝ) ^ ((1 : ℝ) / 10))) hT
  have hsum : (badWindow x : ℝ) ≤ C₁ * (x : ℝ) ^ θ₁ + C₂ * (x : ℝ) ^ θ₂ := by
    unfold badWindow
    linarith
  have hx1r : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hp1 : (x : ℝ) ^ θ₁ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_left _ _)
  have hp2 : (x : ℝ) ^ θ₂ ≤ (x : ℝ) ^ max θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_le hx1r (le_max_right _ _)
  have hm1 : C₁ * (x : ℝ) ^ θ₁ ≤ C₁ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp1 hC₁
  have hm2 : C₂ * (x : ℝ) ^ θ₂ ≤ C₂ * (x : ℝ) ^ max θ₁ θ₂ :=
    mul_le_mul_of_nonneg_left hp2 hC₂
  have hfin : C₁ * (x : ℝ) ^ max θ₁ θ₂ + C₂ * (x : ℝ) ^ max θ₁ θ₂
      = (C₁ + C₂) * (x : ℝ) ^ max θ₁ θ₂ := by ring
  linarith

-- Axiom audit driver for the assembly.
#print axioms theorem51_split

end

end LeanLab.ExceptionalSet.BG2026
