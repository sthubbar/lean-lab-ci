import LeanLab.RamareSaouter2003.Decomp290c

/-!
P0099 p. 16, the height limit in Lemma 4, applied on pp. 19 and 20.
The existing psi-one formula proves the integrated identity.
Mathlib dominated convergence for series then identifies the real height cutoff limit.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.CutoffFormula594

open Filter Real Chebyshev Smooth Thm4Assembly L3Zeta Decomp290c
open scoped Topology

/-- P0099 p. 16, the zero height limit in Lemma 4 at the polynomial weight.
The actual finite-height zero sum tends to the full integrated zero sum.
Mathlib Tannery applies with the summable norms of the actual real zero terms. -/
theorem nearSum_tendsto_total (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Tendsto (nearSum m X u) atTop (𝓝 (∑' i : ZI, zeroTerm m X u i).re) := by
  classical
  have hs := zeroTerm_summable m X u hm hX hu hmu
  have hr := (Complex.hasSum_re hs.hasSum).summable
  rw [Complex.re_tsum hs]
  unfold nearSum
  apply tendsto_tsum_of_dominated_convergence hr.norm
  · intro i
    have hi : ∀ᶠ T : ℝ in atTop, |gZ i| ≤ T := eventually_ge_atTop _
    apply tendsto_const_nhds.congr'
    filter_upwards [hi] with T hT
    simp only [if_pos hT]
  · apply Filter.Eventually.of_forall
    intro T i
    split_ifs <;> simp

/-- P0099 p. 16, the vanishing zero tail after integration by parts.
The actual far real zero sum tends to zero as the real split height increases. -/
theorem farSum_tendsto_zero (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Tendsto (farSum m X u) atTop (𝓝 0) := by
  have hs := zeroTerm_summable m X u hm hX hu hmu
  have hn := nearSum_tendsto_total m X u hm hX hu hmu
  have hz (T : ℝ) : (∑' i : ZI, zeroTerm m X u i).re - nearSum m X u T =
      farSum m X u T := by
    linarith [zero_sum_split m X u T hs]
  have hh := (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (∑' i : ZI, zeroTerm m X u i).re) atTop
      (𝓝 (∑' i : ZI, zeroTerm m X u i).re)).sub hn
  simpa only [hz, sub_self] using hh

/-- P0099 p. 16, the height limit in Lemma 4, at the two affine scales of p. 19.
The integrated explicit formula with the finite near zero sum tends to the
actual weighted psi difference. Its omitted far tail tends to zero. -/
theorem weighted_formula_truncated_tendsto (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Tendsto (fun T : ℝ =>
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      nearSum m X u T -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t)
      atTop (𝓝 (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t)) := by
  rw [weighted_formula_total m X u hm hX hu hmu]
  exact (tendsto_const_nhds.sub (nearSum_tendsto_total m X u hm hX hu hmu)).sub
    tendsto_const_nhds

end LeanLab.RamareSaouter2003.CutoffFormula594

#print axioms LeanLab.RamareSaouter2003.CutoffFormula594.nearSum_tendsto_total

#print axioms LeanLab.RamareSaouter2003.CutoffFormula594.farSum_tendsto_zero

#print axioms LeanLab.RamareSaouter2003.CutoffFormula594.weighted_formula_truncated_tendsto
