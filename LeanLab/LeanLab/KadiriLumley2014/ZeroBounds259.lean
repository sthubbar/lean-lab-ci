/-
P0059 arXiv 1407.7902v1 pages 7 to 9, Lemmas 2.5 and 2.6.
Positive explicit zero-sum bounds. The analytic leaves remain open.
The q function is from arXiv 1310.6374 page 8 Corollary 2.6.
New Prop definitions state paper bounds and require Claude review before merge.
AI wrote this Lean code. CODEX task259. Goldbach is open.
-/
import LeanLab.KadiriLumley2014.ZeroInputs259
import LeanLab.KadiriLumley2014.WeightHigherFactor
import LeanLab.KadiriLumley2014.WeightFirstFactor

namespace LeanLab.KadiriLumley2014.Task259

open Real Set
open Task64 Task92

/-- The q function used by equation 2.40, with the published Rosser constants. -/
noncomputable def countQ (T : ℝ) : ℝ :=
  (0.137 * Real.log T + 0.443) / (T * Real.log T * Real.log (T / (2 * π)))

/-- S1 from equation 2.40. -/
noncomputable def zeroS1 (T1 : ℝ) : ℝ :=
  (1 / (2 * π) + countQ 1132491) * Real.log (T1 / 1132491) *
    Real.log (Real.sqrt (T1 * 1132491) / (2 * π)) + 2 * countRemainder 1132491 / 1132491

/-- S2 from equation 2.41. -/
noncomputable def zeroS2 (m : ℕ) (T1 : ℝ) : ℝ :=
  (1 / (2 * π) + countQ T1) *
    ((1 + m * Real.log (T1 / (2 * π))) / ((m : ℝ) ^ 2 * T1 ^ m) -
      (1 + m * Real.log (30610000000 / (2 * π))) / ((m : ℝ) ^ 2 * 30610000000 ^ m)) +
    2 * countRemainder T1 / T1 ^ (m + 1)

/-- S3 from equation 2.42. -/
noncomputable def zeroS3 (m : ℕ) : ℝ :=
  (1 / (2 * π) + countQ 30610000000) *
    ((1 + m * Real.log (30610000000 / (2 * π))) / ((m : ℝ) ^ 2 * 30610000000 ^ m)) +
    2 * countRemainder 30610000000 / 30610000000 ^ (m + 1)

/-- S4 from equation 2.43. The coefficients belong to the chosen sigma row. -/
noncomputable def zeroS4 (m : ℕ) (c1 c2 c3 : ℝ) : ℝ :=
  (c1 * (1 + 1 / (m : ℝ)) + c2 * Real.log 30610000000 / 30610000000 +
    (c3 + c2 / (m + 1)) / 30610000000) / 30610000000 ^ m

/-- S5 from page 7 display 2.44, repaired by U-1626. The print has R0 over 2 log X0, copied from
Faber Kadiri arXiv 1310.6374 page 10 display 2.30. There J_m is written as z over 2m times K1,
but K1 carries a factor one half, so the substitution gives z over m times K1. The correct
second term has R0 over log X0, twice the print. DECISION U-1626, see Audit1626.
The zero-free constant is the published 5.69693. -/
noncomputable def zeroS5 (X : ℝ) (m : ℕ) (c1 c2 c3 : ℝ) : ℝ :=
  (c1 + c2 * Real.log 30610000000 / 30610000000 + c3 / 30610000000 +
    (c1 + c2 / 30610000000) * 5.69693 / Real.log X *
      (Real.log 30610000000) ^ 2 /
        (((m : ℝ) * 5.69693 / Real.log X) * (Real.log 30610000000) ^ 2 - 1)) /
    30610000000 ^ m

/-- The five positive sum bounds of Lemma 2.5, equations 2.45 to 2.49. -/
def Lemma25Bounds (m : ℕ) (T1 X σ c1 c2 c3 : ℝ) : Prop :=
  positiveZeroSum (fun ρ => if 1132491 < ρ.im ∧ ρ.im ≤ T1 then 1 / ρ.im else 0) ≤ zeroS1 T1 ∧
  positiveZeroSum (fun ρ => if T1 < ρ.im ∧ ρ.im ≤ 30610000000 then 1 / ρ.im ^ (m + 1) else 0) ≤ zeroS2 m T1 ∧
  positiveZeroSum (fun ρ => if 30610000000 < ρ.im then 1 / ρ.im ^ (m + 1) else 0) ≤ zeroS3 m ∧
  positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then 1 / ρ.im ^ (m + 1) else 0) ≤ zeroS4 m c1 c2 c3 ∧
  positiveZeroSum (fun ρ => if 30610000000 < ρ.im ∧ σ < ρ.re then
    X ^ (-1 / (5.69693 * Real.log ρ.im)) / ρ.im ^ (m + 1) else 0) ≤
      zeroS5 X m c1 c2 c3 * X ^ (-1 / (5.69693 * Real.log 30610000000))

/-- LEAF. Page 7 Lemma 2.5. CONDITIONAL ON the explicitly named Theorem 2.4 inputs.
The five estimates are positive bounds, not a nonpositive assertion about Sigma. -/
theorem lemma2_5_positive (m : ℕ) {T1 X σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hX : 10 < X) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000) (hLow : LowZeroData 1132491 2001052 11.637732363)
    (hZF : ZeroFreeRegion 5.69693) (hCount : RosserCountBound)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2) :
    Lemma25Bounds m T1 X σ c1 c2 c3 := by
  sorry

/-- The positive six-term envelope from equation 2.50 with the B coefficients
from equations 2.51, 2.54, 2.58, 2.60, 2.62 and 2.63.
In B1 the Rosser upper count P plus R replaces N of T1. -/
noncomputable def rosserZeroEnvelope (m : ℕ) (δ u X T1 σ c1 c2 c3 : ℝ) : ℝ :=
  let F0 := 1 + δ / 2
  let F1 := firstFactor m δ
  let Fm := higherFactor m δ
  let B0 := min (4 * F1 / ((Real.exp (u / 2) + 1) * δ) * 11.637732363)
    (4 * F0 / (Real.exp (u / 2) + 1) * 2001052)
  let B1 := min (4 * F1 / ((Real.exp (u / 2) + 1) * δ) * zeroS1 T1)
    (4 * F0 / (Real.exp (u / 2) + 1) * (countMain T1 + countRemainder T1 - 2001052))
  let B2 := 2 * Fm / ((Real.exp (u / 2) - 1) * δ ^ m) * zeroS2 m T1
  let B3 := fun s : ℝ => 2 * Fm * (Real.exp (u * s) + 1) /
    (δ ^ m * (Real.exp u - 1)) * zeroS3 m
  let C4 := 2 * (Real.exp u + 1) * Fm / ((Real.exp u - 1) * δ ^ m)
  (B0 + B1 + B2) * X ^ (-(1 / 2 : ℝ)) + B3 σ * X ^ (σ - 1) + B3 (1 - σ) * X ^ (-σ) +
    C4 * zeroS5 X m c1 c2 c3 * X ^ (-1 / (5.69693 * Real.log 30610000000)) +
    C4 * zeroS4 m c1 c2 c3 * X ^ (-1 + 1 / (5.69693 * Real.log 30610000000))

/-- LEAF. Pages 8 and 9 Lemma 2.6. CONDITIONAL ON the actual published zero inputs
and the positive bounds of Lemma 2.5. The Rosser upper count replaces N of T1 in the positive envelope. -/
theorem lemma2_6_positive {m : ℕ} {δ u X T1 σ c1 c2 c3 : ℝ}
    (hm : 2 ≤ m) (hδ : 0 < δ) (hδ1 : δ ≤ 0.0001) (hu : 0 < u) (hu1 : u ≤ 0.0001)
    (hδu : δ = m * u) (hX : 10 < X) (hT0 : 1132491 ≤ T1) (hTH : T1 ≤ 30610000000)
    (hσ : 3 / 5 < σ) (hσ1 : σ < 1)
    (hRH : VerifiedHeight 30610000000) (hLow : LowZeroData 1132491 2001052 11.637732363)
    (hZF : ZeroFreeRegion 5.69693) (hCount : RosserCountBound)
    (hDensity : DensityBound σ c1 c2 c3) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hlog : Real.log X < 5.69693 * m * (Real.log 30610000000) ^ 2)
    (hS : Lemma25Bounds m T1 X σ c1 c2 c3) :
    zeroError m δ u X ≤ rosserZeroEnvelope m δ u X T1 σ c1 c2 c3 := by
  sorry

end LeanLab.KadiriLumley2014.Task259
