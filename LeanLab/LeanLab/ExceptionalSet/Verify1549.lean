/-
P0095 W. C. Lu 2010, Exceptional set of Goldbach number, J. Number Theory 130, 2359-2392.
Unit U-1549, run 20261026T1604Z-17563, T1 VERIFY, falsifier for QUESTION Q-1545a.

Q-1545a: on p. 2369, (39) `Σ_{q ≤ P} W₀(q, 4πN/(qQ), N) ≪ 1` is said to follow from (38)
`Σ_{q ≤ x} N*(α, T, q) ≪ (x² T)^{(12/5+ε)(1-α)}` "and the usual method". The zeros of (39) lie in
the hyperbolic region `q ≤ P = N^{0.1215}`, `q |γ| ≤ K = 4π N^{1/4}`.

This file records, with proofs:
* `rect_exponent_gt_one`: the rectangle `q ≤ P`, `|γ| ≤ K` has `κ (2c + 1/4) > 1`, so (38)
  on one rectangle does not give (39); blockwise in `q` it gives `≪ log N`, see Decomp1545a.
* `rect_exponent_height_small`: at the heights Lu actually needs with an O(1) bound, `N^{0.001}`
  in (40) and (64) and the constant `M`, the rectangle exponent `κ (2c + 0.001)` is `< 1`.
* `li_margin`: the margin `θ · (1/4) < 1` with `θ = 29/10`, for the log-free hyperbolic count of
  H. Z. Li, Acta Arith. 92 (2000), Lemma 6, p. 75, applied with `Y = D ≈ 4π N^{1/4}`.
* `shell_sum_le`: the geometric shell bound that turns a count `≤ B e^{θ(k+1)}` per shell
  `k ≤ λ < k+1` into a total `≤ B e^θ / (1 - e^{θ-s})` when `θ < s`.
and states, as a CITED Prop, `LiHyperbolic`, the shape of that log-free count.

AI wrote this Lean code, Claude, unit U-1549. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.Verify1549

open Real Finset

/-- `c = 0.1215`, p. 2360. -/
noncomputable def cLu : ℝ := 0.1215

/-- `κ = 12/5 + ε` of (37) and (38) with `ε = 1/100`. -/
noncomputable def kap : ℝ := 12 / 5 + 1 / 100

/-- The rectangle `q ≤ N^c`, `|γ| ≤ 4π N^{1/4}` has `(x² T)^κ = N^{κ(2c + 1/4) + o(1)}` with
exponent `2.41 · 0.493 = 1.18813 > 1`, so (38) on this one rectangle gives no saving. -/
theorem rect_exponent_gt_one : 1 < kap * (2 * cLu + 1 / 4) := by
  norm_num [kap, cLu]

/-- At height `T = N^{0.001}`, used in (40) p. 2369 and (64) p. 2380, the rectangle exponent is
`2.41 · 0.244 = 0.58804 < 1`, so (38) and the usual method give `Σ_{q ≤ P} W(q, N^{0.001}, N) ≪ 1`
directly. -/
theorem rect_exponent_height_small : kap * (2 * cLu + 1 / 1000) < 1 := by
  norm_num [kap, cLu]

/-- At a constant height `M`, also used in (64), the exponent is `κ · 2c = 0.58563 < 1`. -/
theorem rect_exponent_height_const : kap * (2 * cLu) < 1 := by
  norm_num [kap, cLu]

/-- The hyperbolic exponent `κ (c + 1/4) = 0.895315 < 1` of `HypRegion` in Decomp1545a. -/
theorem hyp_exponent_lt_one : kap * (cLu + 1 / 4) < 1 := by
  norm_num [kap, cLu]

/-- Li 2000 Lemma 6 gives, for `5 < λ ≤ ε log D`, the count `≤ 279.7 e^{2.9 λ}`. With
`D = (4π N^{1/4})^{1+ε}`, a zero at `β = 1 - λ/log D` has `N^{β-1} = e^{-λ log N / log D}` and
`log N / log D → 4/(1+ε)`. The integral converges because `2.9 < 4`, i.e. `2.9 · (1/4) < 1`. -/
theorem li_margin : (29 / 10 : ℝ) * (1 / 4) < 1 := by norm_num

/-- The shell bound. If the shell `k ≤ λ < k + 1` holds at most `B e^{θ(k+1)}` zeros, and each
contributes at most `e^{-s k}`, the total over any number of shells is at most
`B e^θ / (1 - e^{θ - s})` when `θ < s`. -/
theorem shell_sum_le {B θ s : ℝ} (hB : 0 ≤ B) (hθs : θ < s) (n : ℕ) :
    ∑ k ∈ range n, B * Real.exp (θ * (k + 1)) * Real.exp (-(s * k)) ≤
      B * Real.exp θ / (1 - Real.exp (θ - s)) := by
  set r : ℝ := Real.exp (θ - s) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have h : θ - s < 0 := by linarith
    calc Real.exp (θ - s) < Real.exp 0 := Real.exp_lt_exp.mpr h
      _ = 1 := Real.exp_zero
  have hterm : ∀ k : ℕ, B * Real.exp (θ * (k + 1)) * Real.exp (-(s * k)) =
      B * Real.exp θ * r ^ k := by
    intro k
    rw [hr, ← Real.exp_nat_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hgeom : ∑ k ∈ range n, r ^ k ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
    rw [← Finset.range_eq_Ico, pow_zero] at this
    exact this
  have hBe : 0 ≤ B * Real.exp θ := mul_nonneg hB (Real.exp_pos _).le
  calc B * Real.exp θ * ∑ k ∈ range n, r ^ k ≤ B * Real.exp θ * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left hgeom hBe
    _ = B * Real.exp θ / (1 - r) := by ring

/-- The log-free hyperbolic count, the shape of H. Z. Li, The exceptional set of Goldbach numbers
II, Acta Arith. 92 (2000), Lemma 6, p. 75, Section 3, region (3.1) and count (3.3): for the zeros
of `L(s, χ)`, `χ` primitive mod `q`, `A < q ≤ Y`, `|γ| ≤ D/q`, `D = Y^{1+ε}`, the number with
`β ≥ 1 - λ/log D` is at most `B e^{θ λ}` for `0 ≤ λ ≤ ε log D`, with `θ = 2.9` up to the bounded
range `λ ≤ 5`, absorbed into `B`. For a finite family this is a hypothesis; for the actual zeros
it is CITED, not proved in the lab. The condition `A < q` is kept as `A < q i`. -/
def LiHyperbolic {ι : Type*} (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ)
    (A Y D B θ ε : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → lam ≤ ε * Real.log D →
    ((Z.filter (fun i => A < (q i : ℝ) ∧ (q i : ℝ) ≤ Y ∧ (q i : ℝ) * |γ i| ≤ D ∧
        1 - lam / Real.log D ≤ β i)).card : ℝ) ≤ B * Real.exp (θ * lam)

/-- Vacuity: one zero `q = 1`, `β = 1/2`, `γ = 0`, with `A = 0`, `Y = 1`, `D = e`, `B = 1`,
`θ = 29/10`, `ε = 1/10` satisfies `LiHyperbolic`. -/
theorem vacuity_liHyperbolic :
    LiHyperbolic ({0} : Finset ℕ) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0)
      0 1 (Real.exp 1) 1 (29 / 10) (1 / 10) := by
  intro lam hlam _
  have hexp : (1 : ℝ) ≤ Real.exp (29 / 10 * lam) := by
    apply Real.one_le_exp; positivity
  calc _ ≤ ((({0} : Finset ℕ)).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = 1 := by simp
    _ ≤ 1 * Real.exp (29 / 10 * lam) := by linarith

#print axioms rect_exponent_gt_one
#print axioms rect_exponent_height_small
#print axioms rect_exponent_height_const
#print axioms hyp_exponent_lt_one
#print axioms li_margin
#print axioms shell_sum_le
#print axioms vacuity_liHyperbolic

end LeanLab.ExceptionalSet.Verify1549
