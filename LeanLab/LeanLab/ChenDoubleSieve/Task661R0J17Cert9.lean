import LeanLab.ChenDoubleSieve.Task661CellCore

/-!
Exact ordered cell certificates for Wu 2004 page 26, D2,17.
The parameters are Table 1 row 1 page 30.
The verifier comes from Prove2Me mission 1e48f99d, author kmehltretter82,
Apache 2.0, accepted proof LL_Decomp587l.r0j16_short.
Each theorem below carries its own ordered cell tree inline as a term of the
certificate data type, so this file declares no definition.
AI wrote the new bridges, certificate generators and interval assemblies.
Binary Goldbach is open.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task661
open Wu04Functional Task587
open LeanLab.Ported.Prove2Me.R0J16.SolBuchstabR0J16

/-- Ordered cell certificate for the D2,17 interval 7415648 to 7436876 of phi. -/
theorem j17Bound72 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7415648 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((7436876 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 (.S4 0 (.S4 0 (.S2 1 (.S4 0 .Z .B .B (.S4 0 .B .B .B .B)) .B) (.S2 2 (.S3 1 (.S3 1 .B .B .B) .B (.S2 2 (.S3 1 .B .B (.S3 1 .B .B .B)) (.S3 1 .B .B .B))) (.S3 1 (.S3 1 (.S3 1 .B .B .B) .B .B) .B (.S2 2 .B .I))) (.S3 0 (.S3 0 (.S2 2 (.S3 0 .B .B .B) .B) .B (.S3 0 .B .B .B)) (.S2 3 .B (.S2 3 (.S2 2 .B .I) .I)) (.S3 0 (.S3 0 .B .B .B) (.S2 3 .B .I) (.S3 0 .B .B .B))) (.S2 1 (.S4 0 .B .B .B .I) .I)) (.S3 1 (.S3 1 (.S3 1 (.S3 1 (.S2 2 (.S3 1 .B .B .B) .B) .B (.S3 1 .B .B .B)) .B (.S3 1 (.S3 1 .B .B .B) .B .B)) (.S2 3 .B (.S2 3 (.S2 0 (.S2 3 .B .I) .I) .I)) (.S2 2 (.S3 1 (.S3 1 .B .B .B) .B .B) .I)) (.S2 3 (.S2 3 (.S2 0 .B (.S2 2 .B .B)) (.S2 0 (.S2 2 .B (.S2 3 .B .I)) (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I))) (.S2 3 (.S2 0 (.S2 2 (.S2 3 (.S2 0 .B .I) .I) .I) .I) .I)) (.S2 2 (.S2 2 (.S2 0 (.S3 1 .B (.S2 3 .B .I) .I) .I) .I) .I)) (.S2 2 (.S2 1 (.S3 0 (.S3 0 .B (.S2 3 .B .I) (.S2 2 .B .I)) (.S2 3 (.S2 2 .B .I) .I) .I) .I) .I) (.S2 1 .I .I)) (.S3 1 (.S2 2 (.S2 0 (.S3 1 (.S3 1 (.S3 1 .B .B .B) (.S2 3 .B .I) (.S2 2 (.S2 0 .B .I) .I)) (.S2 3 (.S2 0 (.S2 2 .B .I) .I) .I) .I) .I) (.S2 0 .I .I)) (.S2 3 (.S2 0 (.S2 3 .I .I) .I) (.S2 0 (.S2 3 .I .I) (.S2 3 .I .I))) (.S2 2 (.S2 0 .I .I) (.S2 0 .I .I))) (.S3 0 (.S2 2 (.S2 1 .I .I) (.S2 1 .I .I)) (.S2 3 (.S2 2 .I .I) (.S2 2 .I .I)) (.S2 2 (.S2 1 .I .I) (.S2 1 .I .I))) (.S4 0 (.S2 1 .I .I) (.S2 2 .I .I) (.S2 2 .I .I) (.S2 1 .I .I)))) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 7436876 to 7458104 of phi. -/
theorem j17Bound73 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7436876 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((7458104 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 (.S4 0 .B (.S3 1 .B (.S2 3 .B .I) (.S3 1 .B .I .I)) (.S2 2 (.S2 1 (.S2 2 .B .I) .I) .I) .I) (.S3 1 (.S2 2 (.S2 0 (.S2 2 .B .I) .I) .I) .I .I) (.S3 0 .I .I .I) .I)) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 7458104 to 7500560 of phi. -/
theorem j17Bound74 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7458104 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((7500560 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 (.S4 0 .B .B (.S3 0 .B .I .I) .I) (.S3 1 (.S3 1 .B .I .I) .I .I) .I .I)) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 7500560 to 7585472 of phi. -/
theorem j17Bound75 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7500560 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((7585472 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 .B .I .I .I)) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 7585472 to 7925120 of phi. -/
theorem j17Bound76 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7585472 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((7925120 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 .B .I .I (.S4 0 .I .I .B .B))) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 7925120 to 8604416 of phi. -/
theorem j17Bound77 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((7925120 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((8604416 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 (.S4 0 .I .B .B .B) (.S3 1 .B .B .B) (.S2 1 (.S3 0 .B .B .B) (.S3 0 .B .B .B)) (.S4 0 .B .B .B .B))) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 8604416 to 9963008 of phi. -/
theorem j17Bound78 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((8604416 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((9963008 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 .B .B .B .T)) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 9963008 to 11321600 of phi. -/
theorem j17Bound79 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((9963008 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((11321600 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 .T .T .T .T)) (by decide +kernel)

/-- Ordered cell certificate for the D2,17 interval 11321600 to 12680192 of phi. -/
theorem j17Bound80 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) {φ : ℝ}
    (hlo : ((11321600 : ℝ) / D_grid) ≤ φ) (hhi : φ ≤ ((12680192 : ℝ) / D_grid)) :
    buchstabIntegral ω 2 (fun j => (r0j17_lo j : ℝ)) (fun j => (r0j17_hi j : ℝ)) φ ≤
      ((45791 / 250000000) : ℝ) :=
  j17_interval_bound hω hz hlo hhi (t := (.S4 0 .T .T .T .T)) (by decide +kernel)

end LeanLab.ChenDoubleSieve.Task661
