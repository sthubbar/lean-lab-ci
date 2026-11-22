/-
Cited wall decision for `Task92.costa_pereira` of Decomp92, REREAD U-1741, 2026-11-21.

Target. `Task92.costa_pereira : CostaEstimate`, P0059 Kadiri and Lumley, arXiv 1407.7902v1
page 3 Lemma 2.1 equation 2.9, cited by the paper from Costa Pereira.

Source. N. Costa Pereira, Estimates for the Chebyshev function psi(x) - theta(x),
Math. Comp. 44 (1985) 211-221, Theorem 5, journal page 217 = PDF page 7 of the lab copy
`copies/CostaPereira1985-MathComp44.pdf`, read from the page image, not the text layer.
Printed displays used:
  (30)  psi(x) - theta(x) < 1.001 sqrt x + x^(1/3)   if x >= e^38,
  (32)  psi(x) - theta(x) > 0.999 sqrt x + x^(1/3)   if x >= e^38.
Corrigendum, Math. Comp. 48 (1987) 447, lab copy
`copies/CostaPereira1987-Corrigendum-MathComp48.pdf`: its only fix is Table II on p. 220,
column 1 line 8, the threshold n reads 294 instead of 285. That column is the left endpoint
n of the range n <= x <= 10^8 on which lambda^+ = 1.02117 is claimed. No constant printed in
Theorem 5, in displays (22) to (32), or in the proof constants on p. 217 is changed by it.

Faithfulness. MATCH. `Task64.CostaEstimate` is displays (30) and (32) exactly: the same
coefficients 1.001 and 0.999, the cube root coefficient 1 in both, strict inequalities,
the closed threshold x >= e^38, and Mathlib's standard `Chebyshev.psi` and
`Chebyshev.theta`.

Decision. NAMED HYPOTHESIS for the cited source, `CostaPereiraThm5Named`, which is exactly
`Task64.CostaEstimate`, see the `Iff.rfl` twin below. Costa Pereira proves Theorem 5 from
zero computations of Brent and van de Lune and te Riele through Rosser and Schoenfeld, and
from Tables I and II; the lab does not try to prove it. The sealed leaf
`Task92.costa_pereira` is left unchanged in Decomp92; the conditional assembly below
replaces its use, so the Table 2 row assembly no longer rests on that sorry.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.KadiriLumley2014.Decomp92

namespace LeanLab.KadiriLumley2014.Task92.DQCosta

open Real Set MeasureTheory
open LeanLab.KadiriLumley2014.Task64
open LeanLab.KadiriLumley2014.Task92

/-- NAMED HYPOTHESIS, CITED. Costa Pereira, Math. Comp. 44 (1985) 211-221, Theorem 5,
p. 217, displays (30) and (32): for every real x >= e^38,
0.999 sqrt x + x^(1/3) < psi(x) - theta(x) < 1.001 sqrt x + x^(1/3).
Not touched by the 1987 corrigendum, Math. Comp. 48 p. 447, which fixes only the
threshold 285 -> 294 in Table II p. 220. -/
def CostaPereiraThm5Named : Prop := ∀ x : ℝ, Real.exp 38 ≤ x →
  0.999 * Real.sqrt x + x ^ (1 / 3 : ℝ) < Chebyshev.psi x - Chebyshev.theta x ∧
  Chebyshev.psi x - Chebyshev.theta x < 1.001 * Real.sqrt x + x ^ (1 / 3 : ℝ)

/-- Twin check: the named hypothesis is the lab's transcription `CostaEstimate`. -/
theorem costaPereiraThm5Named_iff : CostaPereiraThm5Named ↔ CostaEstimate := Iff.rfl

/-- The sealed leaf's statement, CONDITIONAL ON the CITED `CostaPereiraThm5Named`. -/
theorem costa_pereira_of_named (hC : CostaPereiraThm5Named) : CostaEstimate := hC

/-- CONDITIONAL ASSEMBLY. Same statement as `Task92.table_row_from_leaves`, with the cited
Costa input taken as the named hypothesis instead of the sorry leaf `costa_pereira`.
CONDITIONAL ON the CITED `CostaPereiraThm5Named` and on the two open leaves
`brun_titchmarsh_tail`, through `brun_titchmarsh_pointwise`, and `table_psi_margin`. -/
theorem table_row_from_leaves_of_named (hC : CostaPereiraThm5Named)
    {r : PrintedRow} (hr : r ∈ tableTwo) :
    KLRow r.threshold r.gapDenom := by
  intro x hx
  obtain ⟨a, ha, hD⟩ := tableTwo_rounding_consistent hr
  have hs := table_small_steps r hr
  have hδ : (0 : ℝ) < r.deltaQ := by exact_mod_cast hs.1
  have hδ1 : (r.deltaQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.1
    norm_num at h ⊢
    exact h
  have hu : 1 / (10 : ℝ) ^ 12 ≤ r.uQ := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.1
    norm_num at h ⊢
    exact h
  have hu1 : (r.uQ : ℝ) ≤ 0.0001 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hs.2.2.2
    norm_num at h ⊢
    exact h
  have hu0 : (0 : ℝ) < r.uQ := by linarith
  have hrpar := (tableTwo_rounding_arithmetic r hr).1
  have haQ : (0 : ℝ) ≤ r.aQ := by exact_mod_cast hrpar.2.2.2.1
  have hbQ : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2 := by
    have hb := (Rat.cast_le (K := ℝ)).mpr hrpar.2.2.2.2.1
    push_cast at hb
    norm_num at hb ⊢
    exact hb
  have ha0 : 0 ≤ a := haQ.trans ha.1
  have ha2 : a ≤ 1 / 2 := ha.2.trans hbQ
  have hxbase : (4 * 10 ^ 18 : ℝ) < x :=
    lt_of_le_of_lt (by
      have h := tableTwo_threshold_ge_base hr
      norm_num [evenBase] at h ⊢
      exact h) hx
  let X : ℝ := x / (Real.exp r.uQ * (1 + (r.deltaQ : ℝ) * (1 - a)))
  obtain ⟨hX0, hX38, hgap, htop⟩ := normalized_domain hδ.le hδ1 hu hu1 ha0 ha2 hxbase
  change 0 < X at hX0
  change Real.exp 38 ≤ X at hX38
  change 1 < X * (Real.exp r.uQ - 1) at hgap
  change Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))) = x at htop
  have htail := brun_titchmarsh_tail (tableTwo_parameters r hr).1 hδ.le hδ1 hu0 hu1
    hX38 hgap ha0 ha2
  have hmargin := table_psi_margin hr ha hD hX38 (by rwa [htop])
  have hpos := central_positive_of_psi_margin (costa_pereira_of_named hC) r.m hδ.le hδ1
    hu0.le hu1 hX38 ha0 ha2 htail hmargin
  obtain ⟨p, hp, hlo, hhi⟩ := prime_of_smoothing hδ hu0.le hX0 ha0 ha2 hpos
  have hB : 1 + (r.deltaQ : ℝ) * (1 - a) ≠ 0 := by
    have : 0 ≤ (r.deltaQ : ℝ) * (1 - a) := mul_nonneg hδ.le (by linarith)
    positivity
  have hlow := lower_endpoint_identity (X := X) hB hD
  rw [htop] at hlow hhi
  exact ⟨p, hp, by rwa [hlow], hhi⟩

end LeanLab.KadiriLumley2014.Task92.DQCosta

#print axioms LeanLab.KadiriLumley2014.Task92.DQCosta.costaPereiraThm5Named_iff
#print axioms LeanLab.KadiriLumley2014.Task92.DQCosta.costa_pereira_of_named
#print axioms LeanLab.KadiriLumley2014.Task92.DQCosta.table_row_from_leaves_of_named
