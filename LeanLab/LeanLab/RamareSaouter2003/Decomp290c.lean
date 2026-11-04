import LeanLab.RamareSaouter2003.Lemma1Zeta

/-!
P0099, Lemma 4 and the zero sum in display 13 on printed p. 19.
The corrected constant in Ramare 2023 Lemma 1.1 cancels in the difference.
AI wrote this Lean code. Binary Goldbach is OPEN.
The four analytic leaves are OPEN. The sum splitting proof is bookkeeping.
-/

namespace LeanLab.RamareSaouter2003.Decomp290c

open Real Chebyshev Smooth Thm4Assembly L3Zeta

/-- The zero term in display 13, printed p. 19, after zero_term_factor. -/
noncomputable def zeroTerm (m : ℕ) (X u : ℝ) (i : ZI) : ℂ :=
  (Complex.exp (u * (i.1 : ℂ)) - 1) / (i.1 : ℂ) * (X : ℂ) ^ (i.1 : ℂ) *
    ∫ t in (0 : ℝ)..1,
      (((1 + (m * u) * t : ℝ) : ℂ) ^ (i.1 : ℂ)) * (fm m t : ℂ)

/-- The near part of the real zero sum, printed pp. 19 and 20, display 15. -/
noncomputable def nearSum (m : ℕ) (X u T : ℝ) : ℝ :=
  ∑' i : ZI, if |gZ i| ≤ T then (zeroTerm m X u i).re else 0

/-- The far part of the real zero sum, printed p. 20, displays 14 and 15. -/
noncomputable def farSum (m : ℕ) (X u T : ℝ) : ℝ :=
  ∑' i : ZI, if T < |gZ i| then (zeroTerm m X u i).re else 0

/-- LEAF. P0099 p. 14, Lemma 2, restricted to T = 1000 and the actual
zero family with multiplicity. This is only summability of the reciprocal
ordinate tail, before the smoothing terms are considered. -/
theorem reciprocal_tail_summable (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      1 / |gZ i| ^ (m + 1) else 0) := by
  sorry

/-- LEAF. P0099 p. 19, the finite near zero part after display 13.
Only finitely many terms have absolute ordinate at most 1000.
This asserts finite support, without estimating their number or size. -/
theorem near_support_finite (m : ℕ) (X u : ℝ) :
    (Function.support (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then
      zeroTerm m X u i else 0)).Finite := by
  sorry

/-- LEAF. P0099 p. 20, display 14 and the bound on exp u rho minus one.
The far zero terms have a fixed nonnegative multiple of the reciprocal
ordinate power as a norm majorant. No summability conclusion is assumed. -/
theorem far_norm_majorant (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ZI,
      ‖if (1000 : ℝ) < |gZ i| then zeroTerm m X u i else 0‖ ≤
        C * (if (1000 : ℝ) < |gZ i| then 1 / |gZ i| ^ (m + 1) else 0) := by
  sorry

/-- Convergence from finite near support, a reciprocal tail and its majorant.
CONDITIONAL ON the three smaller convergence leaves. -/
theorem zeroTerm_summable (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001) :
    Summable (zeroTerm m X u) := by
  classical
  obtain ⟨C, _, hC⟩ := far_norm_majorant m X u hm hX hu hmu
  have htail := (reciprocal_tail_summable m (by omega)).mul_left C
  have hfar : Summable (fun i : ZI => if (1000 : ℝ) < |gZ i| then
      zeroTerm m X u i else 0) := Summable.of_norm_bounded htail hC
  have hnear : Summable (fun i : ZI => if |gZ i| ≤ (1000 : ℝ) then
      zeroTerm m X u i else 0) := summable_of_hasFiniteSupport (near_support_finite m X u)
  convert hnear.add hfar using 1
  funext i
  by_cases h : |gZ i| ≤ (1000 : ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

/-- LEAF. P0099 pp. 15 and 16, Lemma 4, applied as on p. 19 before
 display 13 with delta = m u. Ramare 2023, Lemma 1.1, corrects the constant
 sign. It cancels in this difference. This leaf is the exact weighted formula,
 before the main, zero and logarithmic terms are estimated. The zero sum is not yet split at T. -/
theorem weighted_formula_total (m : ℕ) (X u : ℝ) (hm : 2 ≤ m)
    (hX : 10 ^ 12 ≤ X) (hu : 0 < u) (hmu : (m : ℝ) * u ≤ 0.0001)
    :
    (∫ t in (0 : ℝ)..1, Dψ X u (m * u) t * fm m t) =
      (∫ t in (0 : ℝ)..1,
        (Real.exp u * (1 + m * u * t) * X - (1 + m * u * t) * X) * fm m t) -
      (∑' i : ZI, zeroTerm m X u i).re -
        ∫ t in (0 : ℝ)..1,
          (1 / 2) * (Real.log (1 - 1 / (Real.exp u * ((1 + m * u * t) * X)) ^ 2) -
            Real.log (1 - 1 / ((1 + m * u * t) * X) ^ 2)) * fm m t := by
  sorry

/-- Splitting the actual zero sum at T. The only premise is summability.
This applies Mathlib's real part and indicator identities. -/
theorem zero_sum_split (m : ℕ) (X u T : ℝ) (hs : Summable (zeroTerm m X u)) :
    (∑' i : ZI, zeroTerm m X u i).re = nearSum m X u T + farSum m X u T := by
  classical
  have hr := (Complex.hasSum_re hs.hasSum).summable
  have hn := hr.indicator {i : ZI | |gZ i| ≤ T}
  have hf := hr.indicator {i : ZI | T < |gZ i|}
  rw [Complex.re_tsum hs]
  change _ = (∑' i : ZI, Set.indicator {i : ZI | |gZ i| ≤ T}
    (fun i => (zeroTerm m X u i).re) i) +
    ∑' i : ZI, Set.indicator {i : ZI | T < |gZ i|}
      (fun i => (zeroTerm m X u i).re) i
  rw [← hn.tsum_add hf]
  apply tsum_congr
  intro i
  by_cases h : |gZ i| ≤ T
  · simp [Set.indicator, h, not_lt.mpr h]
  · simp [Set.indicator, h, lt_of_not_ge h]

end LeanLab.RamareSaouter2003.Decomp290c

#print axioms LeanLab.RamareSaouter2003.Decomp290c.reciprocal_tail_summable
#print axioms LeanLab.RamareSaouter2003.Decomp290c.near_support_finite
#print axioms LeanLab.RamareSaouter2003.Decomp290c.far_norm_majorant
#print axioms LeanLab.RamareSaouter2003.Decomp290c.zeroTerm_summable
#print axioms LeanLab.RamareSaouter2003.Decomp290c.weighted_formula_total
#print axioms LeanLab.RamareSaouter2003.Decomp290c.zero_sum_split
