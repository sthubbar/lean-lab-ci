/-
P0059 arXiv 1407.7902v1 pages 5 and 6 Theorem 2.4, page 11 Theorem 3.2.
Published zero inputs are cited external leaves. They are not proved here.
New Prop definitions state the paper inputs and require Claude review before merge.
AI wrote this Lean code. CODEX task259. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroDefinitions259
import LeanLab.KadiriLumley2014.TableCertificates259

namespace LeanLab.KadiriLumley2014.Task259

open Real Set

/-- Sum over positive ordinates of actual strip zeros, with analytic multiplicity. -/
noncomputable def positiveZeroSum (f : ℂ → ℝ) : ℝ :=
  ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1},
    if 0 < (ρ : ℂ).im then (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * f ρ else 0

/-- N of T counts positive ordinates strictly below T, as defined in Section 2.5. -/
noncomputable def zeroCount (T : ℝ) : ℝ :=
  positiveZeroSum (fun ρ => if ρ.im < T then 1 else 0)

/-- N of sigma and T counts the zeros strictly to the right of sigma and below T. -/
noncomputable def densityCount (σ T : ℝ) : ℝ :=
  positiveZeroSum (fun ρ => if σ < ρ.re ∧ ρ.im < T then 1 else 0)

/-- The main term P of the zero count in equation 2.32. -/
noncomputable def countMain (T : ℝ) : ℝ :=
  T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8

/-- The Rosser error R with the constants in Theorem 3.2 part d. -/
noncomputable def countRemainder (T : ℝ) : ℝ :=
  0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

/-- The verified-height statement in Theorem 2.4 part a. -/
def VerifiedHeight (H : ℝ) : Prop :=
  ∀ z : ℂ, riemannZeta z = 0 → 0 ≤ z.re → z.re ≤ 1 →
    0 ≤ z.im → z.im ≤ H → z.re = 1 / 2

/-- The low-zero information in equations 2.29 and 2.30. -/
def LowZeroData (T0 N0 S0 : ℝ) : Prop :=
  positiveZeroSum (fun ρ => if ρ.re = 1 / 2 ∧ ρ.im ≤ T0 then 1 else 0) ≤ N0 ∧
    zeroCount T0 = N0 ∧
    positiveZeroSum (fun ρ => if ρ.re = 1 / 2 ∧ ρ.im ≤ T0 then 1 / ρ.im else 0) ≤ S0

/-- The zero-free region in equation 2.31. -/
def ZeroFreeRegion (R0 : ℝ) : Prop :=
  ∀ z : ℂ, 2 ≤ |z.im| → 1 - 1 / (R0 * Real.log |z.im|) ≤ z.re → riemannZeta z ≠ 0

/-- The published zero-count error in equation 2.32 with the Rosser constants. -/
def RosserCountBound : Prop :=
  ∀ T : ℝ, 2 ≤ T → |zeroCount T - countMain T| ≤ countRemainder T

/-- The zero-density estimate in equation 2.33 with fixed H from Theorem 3.2. -/
def DensityBound (σ c1 c2 c3 : ℝ) : Prop :=
  ∀ T : ℝ, 30610000000 ≤ T → densityCount σ T ≤ c1 * T + c2 * Real.log T + c3

/-- LEAF. Page 11 Theorem 3.2 part a. Cited Platt 2011 finite-height RH verification. -/
theorem published_verified_height : VerifiedHeight 30610000000 := by
  sorry

/-- LEAF. Page 11 Theorem 3.2 part b. Cited computation using Odlyzko's zero list. -/
theorem published_low_zero_data : LowZeroData 1132491 2001052 11.637732363 := by
  sorry

/-- LEAF. Page 11 Theorem 3.2 part c. Cited Kadiri 2005 Theorem 1.1. -/
theorem published_zero_free_region : ZeroFreeRegion 5.69693 := by
  sorry

/-- LEAF. Page 11 Theorem 3.2 part d. Cited Rosser 1941 Theorem 19. -/
theorem published_zero_count : RosserCountBound := by
  sorry

/-- LEAF. Page 11 Theorem 3.2 part e and Table 1. Cited Kadiri 2013. -/
theorem published_zero_density {r : ℕ × ℚ × ℚ × ℚ} (hr : r ∈ densityTable) :
    DensityBound ((r.1 : ℝ) / 100) r.2.1 r.2.2.1 r.2.2.2 := by
  sorry

end LeanLab.KadiriLumley2014.Task259
