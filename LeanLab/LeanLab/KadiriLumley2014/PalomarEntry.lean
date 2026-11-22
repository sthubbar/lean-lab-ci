/-
P0059 Kadiri and Lumley 2014, Corollary 1.2 as a conditional Palomar entry.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing new about it.
Every external input is an explicit hypothesis, so the file does not use the sorry leaves
costa_pereira, brun_titchmarsh_pointwise, table_endpoint_budget or oesilva_even.
The proofs replay table_zero_budget, table_psi_margin and table_row_from_leaves of
Decomp92 with the endpoint budget, the Costa estimate and the Brun Titchmarsh bound
supplied as hypotheses.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.KadiriLumley2014.RowDefinition92
import LeanLab.KadiriLumley2014.Decomp92
import LeanLab.KadiriLumley2014.Corollary
import LeanLab.KadiriLumley2014.CostaSplit
import LeanLab.KadiriLumley2014.BrunTitchmarshMV

namespace LeanLab.KadiriLumley2014.PalomarEntry
open Real Set MeasureTheory
open LeanLab.KadiriLumley2014.Task64 LeanLab.KadiriLumley2014.Task92

/-- One Table 2 row, from the Costa estimate, the Montgomery Vaughan Brun Titchmarsh
inequality and the endpoint budget of display 2.64 at this row, the exact conclusion of
table_endpoint_budget. No sorry leaf is used. AI wrote this Lean code. -/
theorem row_of_inputs (hC : CostaEstimate)
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    {r : PrintedRow} (hr : r ∈ tableTwo)
    (hE : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
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
  have htail : tailThetaIntegral r.m r.deltaQ r.uQ X a ≤
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a :=
    tail_bound_of_pointwise r.m hδ.le ((Real.exp_pos 38).le.trans hX38) ha0 ha2
      (fun t ht => BrunTitchmarshMV.brun_titchmarsh_pointwise_of_MV hMV hδ.le hδ1 hu0 hu1
        hX38 hgap ht)
  -- replay of table_zero_budget with hE in place of table_endpoint_budget
  have hxX : r.threshold < Real.exp r.uQ * (X * (1 + (r.deltaQ : ℝ) * (1 - a))) := by
    rwa [htop]
  obtain ⟨hY38, hYX, hgapY⟩ := rowEndpointX_domain hr ha hX38 hxX
  have hm : 0 < r.m := by have := (tableTwo_parameters r hr).1; omega
  have hb := zero_budget_of_endpoint hm hδ hu0 ha0 ha.2 hbQ hY38 hYX hgapY hE
  -- replay of table_psi_margin
  have hl := (smoothed_explicit_lower (tableTwo_parameters r hr).1 hδ hδ1 hu0 hu1 hX38).2
  have hmargin : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient r.deltaQ r.uQ X * tailMass r.m a /
        (∫ t in (0 : ℝ)..1, weight r.m t) < psiAverage r.m r.deltaQ r.uQ X := by
    linarith
  have hpos := central_positive_of_psi_margin hC r.m hδ.le hδ1 hu0.le hu1
    hX38 ha0 ha2 htail hmargin
  obtain ⟨p, hp, hlo, hhi⟩ := prime_of_smoothing hδ hu0.le hX0 ha0 ha2 hpos
  have hB : 1 + (r.deltaQ : ℝ) * (1 - a) ≠ 0 := by
    have : 0 ≤ (r.deltaQ : ℝ) * (1 - a) := mul_nonneg hδ.le (by linarith)
    positivity
  have hlow := lower_endpoint_identity (X := X) hB hD
  rw [htop] at hlow hhi
  exact ⟨p, hp, by rwa [hlow], hhi⟩

/-- P0059 Corollary 1.2, a conditional Palomar entry: every odd n with
5 < n < 1966196911 * 4 * 10^18 is a sum of three primes. AI wrote this Lean code.
Named inputs, each an explicit hypothesis:
hEven, the Oliveira e Silva, Herzog and Pardi 2014 verification of even Goldbach to 4e18;
hMV, Montgomery and Vaughan 1973 Theorem 2, the Brun Titchmarsh inequality;
hDus, Dusart 2010 Theorem 5.2 row eta_2 = 0.05, giving the Costa estimate through
CostaSplit.costa_of_dusart;
h0 and h60, display 2.64 with the true zero sum at the Table 2 rows log 4e18 and 60 only.
Research for burst-20261115 found that row 60 holds numerically only if the zeros above
height 3.061e10 lie on the critical line. -/
theorem corollary1_2_of_inputs (hEven : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hMV : LeanLab.RamareSaouter2003.Thm4Parts.MVBrunTitchmarsh)
    (hDus : ∀ t : ℝ, 122568683 ≤ t →
      |Chebyshev.theta t - t| < 0.05 * t / Real.log t ^ 2)
    (h0 : let r : PrintedRow := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r)))
    (h60 : let r : PrintedRow := ⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩
      (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
        tailCoefficient r.deltaQ r.uQ (rowEndpointX r) *
            tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
          (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
        (Real.exp r.uQ - 1) * rowEndpointX r *
          (1 + (r.deltaQ : ℝ) / 2 - zeroError r.m r.deltaQ r.uQ (rowEndpointX r))) :
    ∀ n : ℕ, Odd n → 5 < n → n < 1966196911 * (4 * 10 ^ 18) → IsTernarySum n := by
  have hC : CostaEstimate := CostaSplit.costa_of_dusart hDus
  have r0 : KLRow (4 * 10 ^ 18) 36082898 := by
    convert (row_of_inputs hC hMV
      (r := ⟨0, 5, 35800, 272519712, 92, 2129, 36082898⟩) (by decide +kernel) h0)
      using 1 <;> norm_num [Task64.PrintedRow.threshold, Task64.evenBase]
  have r60 : KLRow (Real.exp 60) 1966196911 := by
    convert (row_of_inputs hC hMV
      (r := ⟨60, 61, 4588, 20504393735, 93, 4527, 1966196911⟩) (by decide +kernel) h60)
      using 1 <;> norm_num [Task64.PrintedRow.threshold, Task64.evenBase]
  exact corollary1_2_of r0 r60 hEven

end LeanLab.KadiriLumley2014.PalomarEntry
