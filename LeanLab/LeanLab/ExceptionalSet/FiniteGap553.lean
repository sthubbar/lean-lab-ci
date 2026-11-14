import LeanLab.ExceptionalSet.FourierTransport553

/-!
P0082 page370 after display41. The finite localization implication.
The approximation and unfiltered phase bounds remain explicit hypotheses.
The integer height comes from the Fourier cutoff.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.FiniteGap553
open Finset

/-- P0082 page370 after display41, derived finite localization step.
A large smoothed phase lies near a half integer in the actual Fourier cutoff. -/
theorem finite_fourier_gap (H : ℕ) (c : ℤ → ℂ) (φ : ℝ → ℂ) (Z : ℂ)
    (t r err L U : ℝ) (hU : 0 ≤ U)
    (happrox : ‖Z - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * φ (t + h / 2)‖ ≤ err)
    (hc : (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ L)
    (hsmall : ∀ h ∈ Finset.Icc (-(H : ℤ)) H,
      r < |t + h / 2| → ‖φ (t + h / 2)‖ ≤ U)
    (hlarge : err + L * U < ‖Z‖) :
    ∃ h : ℤ, (|h| : ℝ) ≤ H ∧ |t - h / 2| ≤ r := by
  obtain ⟨k, hk, hbig⟩ := FourierTransport553.large_value_transport
    (Finset.Icc (-(H : ℤ)) H) c (fun h => φ (t + h / 2))
    Z err L U hU happrox hc hlarge
  have hnear : |t + k / 2| ≤ r := by
    by_contra hno
    exact (not_lt_of_ge (hsmall k hk (lt_of_not_ge hno))) hbig
  refine ⟨-k, ?_, ?_⟩
  · have habs : |k| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hk)
    exact_mod_cast (show |-k| ≤ (H : ℤ) by simpa only [abs_neg] using habs)
  · simpa only [Int.cast_neg, neg_div, sub_neg_eq_add] using hnear

end LeanLab.ExceptionalSet.FiniteGap553
