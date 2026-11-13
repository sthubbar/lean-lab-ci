import LeanLab.ChenDoubleSieve.Burst9Psi2Panels

/-!
# Burst 9: the 52 bounds `I_{2,i}(row) ≤ U`, Wu 2004 Lemma 5.2, page 26

Source: Wu 2004, arXiv 0705.1652, Lemma 5.2, pages 25 and 26, the integrals `I_{2,9}` to
`I_{2,21}` and the domains `D_{2,9}` to `D_{2,21}`; Table 1, page 30, the four rows using
Proposition 4. Index `j : Fin 13` of `Wu04Functional.I2` is `I_{2,j+9}`.

Every statement assumes `IsBuchstab ω` and `ZeroBelowOne ω`. The second is Wu's implicit
convention: `ω(u) = 0` for `u < 1`, the main term of Lemma 2.10, page 9, when `y > x`. Without it
the arguments `(φ − t − ⋯)/x` that fall below 1, see `last_I2_range_witness`, make the values
depend on an unconstrained part of `ω`. This is recorded as a QUESTION in the note.

20 of the 52 bounds are PROVED from `buchstabSup_le_box`: the 14 degenerate domains of rows 3
and 4, where `κ₃ = s`, have value 0, and six small domains of rows 1 and 2 fit the slack. The
other 32 are LEAF declarations, each a single certified quadrature statement whose bound is a
scipy recomputation plus 0.1 percent.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst9Psi2
open Wu04Functional

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,9}` defining `I_{2,9}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.013922576`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.013908667`; the bound adds 0.1 percent. -/
theorem I2_r0_9 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 0 ≤ (870161/62500000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,10}` defining `I_{2,10}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.009342453`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.009333120`; the bound adds 0.1 percent. -/
theorem I2_r0_10 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 1 ≤ (9342453/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,11}` defining `I_{2,11}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.004545138`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.004540597`; the bound adds 0.1 percent. -/
theorem I2_r0_11 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 2 ≤ (2272569/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,12}` defining `I_{2,12}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.007085137`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.007078059`; the bound adds 0.1 percent. -/
theorem I2_r0_12 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 3 ≤ (7085137/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,13}` defining `I_{2,13}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.024633499`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.024608890`; the bound adds 0.1 percent. -/
theorem I2_r0_13 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 4 ≤ (24633499/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,14}` defining `I_{2,14}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.014345377`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.014331046`; the bound adds 0.1 percent. -/
theorem I2_r0_14 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 5 ≤ (14345377/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,15}` defining `I_{2,15}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.005296024`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.005290733`; the bound adds 0.1 percent. -/
theorem I2_r0_15 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 6 ≤ (662003/125000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,16}` defining `I_{2,16}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.000074908`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000074833`; the bound adds 0.1 percent. -/
theorem I2_r0_16 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 7 ≤ (18727/250000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,17}` defining `I_{2,17}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.000183164`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000182981`; the bound adds 0.1 percent. -/
theorem I2_r0_17 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 8 ≤ (45791/250000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,18}` defining `I_{2,18}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.000155569`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000155414`; the bound adds 0.1 percent. -/
theorem I2_r0_18 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 9 ≤ (155569/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,19}` defining `I_{2,19}(s, s', κ₁, κ₂, κ₃)`, for row 1 of Table 1,
`s = 2.2, s' = 4.54, κ₁ = 3.53, κ₂ = 2.90, κ₃ = 2.44`, is at most `0.000070737`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000070666`; the bound adds 0.1 percent. -/
theorem I2_r0_19 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 10 ≤ (70737/1000000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,20}` for row 1 of Table 1 is at most `6.515e-05`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r0_20 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 11 ≤ (14904/228765625 : ℝ) := by
  have e : I2 ω (tableParams 0) 11 = buchstabSup ω 3 (![1/(tableParams 0).k2, 1/(tableParams 0).k3, 1/(tableParams 0).k3, 1/(tableParams 0).k3, 1/(tableParams 0).k3]) (![1/(tableParams 0).k3, 1/(tableParams 0).s, 1/(tableParams 0).s, 1/(tableParams 0).s, 1/(tableParams 0).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 3)
    ((![1/(tableParams 0).k2, 1/(tableParams 0).k3, 1/(tableParams 0).k3, 1/(tableParams 0).k3, 1/(tableParams 0).k3]) : Fin (3 + 2) → ℝ) ((![1/(tableParams 0).k3, 1/(tableParams 0).s, 1/(tableParams 0).s, 1/(tableParams 0).s, 1/(tableParams 0).s]) : Fin (3 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,21}` for row 1 of Table 1 is at most `4.113e-06`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r0_21 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 0) 12 ≤ (2846016/692016015625 : ℝ) := by
  have e : I2 ω (tableParams 0) 12 = buchstabSup ω 4 (fun _ => 1/(tableParams 0).k3) (fun _ => 1/(tableParams 0).s) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 4)
    ((fun _ => 1/(tableParams 0).k3) : Fin (4 + 2) → ℝ) ((fun _ => 1/(tableParams 0).s) : Fin (4 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,9}` defining `I_{2,9}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.014713151`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.014698453`; the bound adds 0.1 percent. -/
theorem I2_r1_9 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 0 ≤ (14713151/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,10}` defining `I_{2,10}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.008347739`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.008339400`; the bound adds 0.1 percent. -/
theorem I2_r1_10 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 1 ≤ (8347739/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,11}` defining `I_{2,11}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.004589086`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.004584501`; the bound adds 0.1 percent. -/
theorem I2_r1_11 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 2 ≤ (2294543/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,12}` defining `I_{2,12}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.003417039`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.003413625`; the bound adds 0.1 percent. -/
theorem I2_r1_12 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 3 ≤ (3417039/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,13}` defining `I_{2,13}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.020031169`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.020011158`; the bound adds 0.1 percent. -/
theorem I2_r1_13 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 4 ≤ (20031169/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,14}` defining `I_{2,14}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.009167311`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.009158153`; the bound adds 0.1 percent. -/
theorem I2_r1_14 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 5 ≤ (9167311/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,15}` defining `I_{2,15}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.002887983`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.002885098`; the bound adds 0.1 percent. -/
theorem I2_r1_15 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 6 ≤ (2887983/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,16}` defining `I_{2,16}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.000070786`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000070715`; the bound adds 0.1 percent. -/
theorem I2_r1_16 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 7 ≤ (35393/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,17}` defining `I_{2,17}(s, s', κ₁, κ₂, κ₃)`, for row 2 of Table 1,
`s = 2.3, s' = 4.50, κ₁ = 3.54, κ₂ = 2.88, κ₃ = 2.43`, is at most `0.000092979`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000092886`; the bound adds 0.1 percent. -/
theorem I2_r1_17 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 8 ≤ (92979/1000000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,18}` for row 2 of Table 1 is at most `2.662e-04`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r1_18 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 9 ≤ (169/634800 : ℝ) := by
  have e : I2 ω (tableParams 1) 9 = buchstabSup ω 2 (![1/(tableParams 1).k2, 1/(tableParams 1).k2, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) (![1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).s, 1/(tableParams 1).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 1).k2, 1/(tableParams 1).k2, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).s, 1/(tableParams 1).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,19}` for row 2 of Table 1 is at most `1.006e-04`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r1_19 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 10 ≤ (1957527/19467200000 : ℝ) := by
  have e : I2 ω (tableParams 1) 10 = buchstabSup ω 2 (![1/(tableParams 1).k1, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) (![1/(tableParams 1).k2, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 1).k1, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 1).k2, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,20}` for row 2 of Table 1 is at most `4.593e-06`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r1_20 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 11 ≤ (257049/55968200000 : ℝ) := by
  have e : I2 ω (tableParams 1) 11 = buchstabSup ω 3 (![1/(tableParams 1).k2, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) (![1/(tableParams 1).k3, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 3)
    ((![1/(tableParams 1).k2, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3, 1/(tableParams 1).k3]) : Fin (3 + 2) → ℝ) ((![1/(tableParams 1).k3, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s, 1/(tableParams 1).s]) : Fin (3 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,21}` for row 2 of Table 1 is at most `7.923e-08`, by
the box bound of `buchstabSup_le_box`. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r1_21 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 1) 12 ≤ (1172914587/14803588900000000 : ℝ) := by
  have e : I2 ω (tableParams 1) 12 = buchstabSup ω 4 (fun _ => 1/(tableParams 1).k3) (fun _ => 1/(tableParams 1).s) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 4)
    ((fun _ => 1/(tableParams 1).k3) : Fin (4 + 2) → ℝ) ((fun _ => 1/(tableParams 1).s) : Fin (4 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,9}` defining `I_{2,9}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.017267618`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.017250368`; the bound adds 0.1 percent. -/
theorem I2_r2_9 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 0 ≤ (8633809/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,10}` defining `I_{2,10}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.007429622`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.007422200`; the bound adds 0.1 percent. -/
theorem I2_r2_10 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 1 ≤ (3714811/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,11}` defining `I_{2,11}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.005342719`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.005337382`; the bound adds 0.1 percent. -/
theorem I2_r2_11 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 2 ≤ (5342719/1000000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,12}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_12 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 3 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 3 = buchstabSup ω 1 (![1/(tableParams 2).sp, 1/(tableParams 2).sp, 1/(tableParams 2).k3]) (![1/(tableParams 2).k1, 1/(tableParams 2).k1, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 1)
    ((![1/(tableParams 2).sp, 1/(tableParams 2).sp, 1/(tableParams 2).k3]) : Fin (1 + 2) → ℝ) ((![1/(tableParams 2).k1, 1/(tableParams 2).k1, 1/(tableParams 2).s]) : Fin (1 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,13}` defining `I_{2,13}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.015670048`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.015654394`; the bound adds 0.1 percent. -/
theorem I2_r2_13 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 4 ≤ (489689/31250000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,14}` defining `I_{2,14}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.005449100`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.005443656`; the bound adds 0.1 percent. -/
theorem I2_r2_14 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 5 ≤ (54491/10000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,15}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_15 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 6 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 6 = buchstabSup ω 1 (![1/(tableParams 2).k1, 1/(tableParams 2).k2, 1/(tableParams 2).k3]) (![1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 1)
    ((![1/(tableParams 2).k1, 1/(tableParams 2).k2, 1/(tableParams 2).k3]) : Fin (1 + 2) → ℝ) ((![1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).s]) : Fin (1 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,16}` defining `I_{2,16}(s, s', κ₁, κ₂, κ₃)`, for row 3 of Table 1,
`s = 2.4, s' = 4.46, κ₁ = 3.57, κ₂ = 2.87, κ₃ = 2.40`, is at most `0.000085942`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000085856`; the bound adds 0.1 percent. -/
theorem I2_r2_16 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 7 ≤ (42971/500000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,17}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_17 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 8 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 8 = buchstabSup ω 2 (![1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k3]) (![1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,18}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_18 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 9 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 9 = buchstabSup ω 2 (![1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) (![1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).s, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 2).k2, 1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).s, 1/(tableParams 2).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,19}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_19 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 10 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 10 = buchstabSup ω 2 (![1/(tableParams 2).k1, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) (![1/(tableParams 2).k2, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 2).k1, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 2).k2, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,20}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_20 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 11 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 11 = buchstabSup ω 3 (![1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) (![1/(tableParams 2).k3, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 3)
    ((![1/(tableParams 2).k2, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3, 1/(tableParams 2).k3]) : Fin (3 + 2) → ℝ) ((![1/(tableParams 2).k3, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s, 1/(tableParams 2).s]) : Fin (3 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,21}` for row 3 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r2_21 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 2) 12 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 2) 12 = buchstabSup ω 4 (fun _ => 1/(tableParams 2).k3) (fun _ => 1/(tableParams 2).s) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 4)
    ((fun _ => 1/(tableParams 2).k3) : Fin (4 + 2) → ℝ) ((fun _ => 1/(tableParams 2).s) : Fin (4 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,9}` defining `I_{2,9}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.012408337`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.012395941`; the bound adds 0.1 percent. -/
theorem I2_r3_9 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 0 ≤ (12408337/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,10}` defining `I_{2,10}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.005420726`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.005415311`; the bound adds 0.1 percent. -/
theorem I2_r3_10 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 1 ≤ (2710363/500000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,11}` defining `I_{2,11}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.003643194`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.003639554`; the bound adds 0.1 percent. -/
theorem I2_r3_11 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 2 ≤ (1821597/500000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,12}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_12 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 3 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 3 = buchstabSup ω 1 (![1/(tableParams 3).sp, 1/(tableParams 3).sp, 1/(tableParams 3).k3]) (![1/(tableParams 3).k1, 1/(tableParams 3).k1, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 1)
    ((![1/(tableParams 3).sp, 1/(tableParams 3).sp, 1/(tableParams 3).k3]) : Fin (1 + 2) → ℝ) ((![1/(tableParams 3).k1, 1/(tableParams 3).k1, 1/(tableParams 3).s]) : Fin (1 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,13}` defining `I_{2,13}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.008106273`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.008098175`; the bound adds 0.1 percent. -/
theorem I2_r3_13 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 4 ≤ (8106273/1000000000 : ℝ) := by
  sorry

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,14}` defining `I_{2,14}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.002640381`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.002637743`; the bound adds 0.1 percent. -/
theorem I2_r3_14 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 5 ≤ (2640381/1000000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,15}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_15 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 6 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 6 = buchstabSup ω 1 (![1/(tableParams 3).k1, 1/(tableParams 3).k2, 1/(tableParams 3).k3]) (![1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 1)
    ((![1/(tableParams 3).k1, 1/(tableParams 3).k2, 1/(tableParams 3).k3]) : Fin (1 + 2) → ℝ) ((![1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).s]) : Fin (1 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- LEAF. Wu 2004 Lemma 5.2, page 26: the maximum over `φ ≥ 2` of the Buchstab integral over
`D_{2,16}` defining `I_{2,16}(s, s', κ₁, κ₂, κ₃)`, for row 4 of Table 1,
`s = 2.5, s' = 4.12, κ₁ = 3.56, κ₂ = 2.91, κ₃ = 2.50`, is at most `0.000043202`.
One certified quadrature: Wu evaluated it numerically for Table 1, page 30. A scipy recomputation
with the exact ω, zero below one, gave `0.000043159`; the bound adds 0.1 percent. -/
theorem I2_r3_16 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 7 ≤ (21601/500000000 : ℝ) := by
  sorry

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,17}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_17 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 8 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 8 = buchstabSup ω 2 (![1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k3]) (![1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,18}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_18 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 9 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 9 = buchstabSup ω 2 (![1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) (![1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).s, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 3).k2, 1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).s, 1/(tableParams 3).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,19}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_19 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 10 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 10 = buchstabSup ω 2 (![1/(tableParams 3).k1, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) (![1/(tableParams 3).k2, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 2)
    ((![1/(tableParams 3).k1, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) : Fin (2 + 2) → ℝ) ((![1/(tableParams 3).k2, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s]) : Fin (2 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,20}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_20 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 11 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 11 = buchstabSup ω 3 (![1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) (![1/(tableParams 3).k3, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s]) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 3)
    ((![1/(tableParams 3).k2, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3, 1/(tableParams 3).k3]) : Fin (3 + 2) → ℝ) ((![1/(tableParams 3).k3, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s, 1/(tableParams 3).s]) : Fin (3 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- Wu 2004 Lemma 5.2, page 26: `I_{2,21}` for row 4 of Table 1 is at most `0.000e+00`, by
degenerate, one coordinate is pinned since κ₃ = s, so the bound is 0. CONDITIONAL ON IsBuchstab and ZeroBelowOne, through `ω ≤ 1`. PROVED. -/
theorem I2_r3_21 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    I2 ω (tableParams 3) 12 ≤ (0/1 : ℝ) := by
  have e : I2 ω (tableParams 3) 12 = buchstabSup ω 4 (fun _ => 1/(tableParams 3).k3) (fun _ => 1/(tableParams 3).s) := rfl
  have hb := buchstabSup_le_box (extended_buchstab_le_one hω hz) (n := 4)
    ((fun _ => 1/(tableParams 3).k3) : Fin (4 + 2) → ℝ) ((fun _ => 1/(tableParams 3).s) : Fin (4 + 2) → ℝ)
    (by intro j; fin_cases j <;> norm_num [tableParams])
    (by intro j; fin_cases j <;> norm_num [tableParams])
  rw [e]
  refine hb.trans ?_
  norm_num [tableParams, Fin.prod_univ_succ]

/-- The thirteen `I₂` bounds of row 1 summed. -/
theorem I2_sum_row0 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∑ j, I2 ω (tableParams 0) j ≤ (70617826659731/885780500000000 : ℝ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  have := add_le_add (I2_r0_9 hω hz) (add_le_add (I2_r0_10 hω hz) (add_le_add (I2_r0_11 hω hz)
    (add_le_add (I2_r0_12 hω hz) (add_le_add (I2_r0_13 hω hz) (add_le_add (I2_r0_14 hω hz)
    (add_le_add (I2_r0_15 hω hz) (add_le_add (I2_r0_16 hω hz) (add_le_add (I2_r0_17 hω hz)
    (add_le_add (I2_r0_18 hω hz) (add_le_add (I2_r0_19 hω hz) (add_le_add (I2_r0_20 hω hz)
    (I2_r0_21 hω hz))))))))))))
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by norm_num)))
  rfl

/-- The thirteen `I₂` bounds of row 2 summed. -/
theorem I2_sum_row1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∑ j, I2 ω (tableParams 1) j ≤ (14142319035748283/222053833500000000 : ℝ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  have := add_le_add (I2_r1_9 hω hz) (add_le_add (I2_r1_10 hω hz) (add_le_add (I2_r1_11 hω hz)
    (add_le_add (I2_r1_12 hω hz) (add_le_add (I2_r1_13 hω hz) (add_le_add (I2_r1_14 hω hz)
    (add_le_add (I2_r1_15 hω hz) (add_le_add (I2_r1_16 hω hz) (add_le_add (I2_r1_17 hω hz)
    (add_le_add (I2_r1_18 hω hz) (add_le_add (I2_r1_19 hω hz) (add_le_add (I2_r1_20 hω hz)
    (I2_r1_21 hω hz))))))))))))
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by norm_num)))
  rfl

/-- The thirteen `I₂` bounds of row 3 summed. -/
theorem I2_sum_row2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∑ j, I2 ω (tableParams 2) j ≤ (51245049/1000000000 : ℝ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  have := add_le_add (I2_r2_9 hω hz) (add_le_add (I2_r2_10 hω hz) (add_le_add (I2_r2_11 hω hz)
    (add_le_add (I2_r2_12 hω hz) (add_le_add (I2_r2_13 hω hz) (add_le_add (I2_r2_14 hω hz)
    (add_le_add (I2_r2_15 hω hz) (add_le_add (I2_r2_16 hω hz) (add_le_add (I2_r2_17 hω hz)
    (add_le_add (I2_r2_18 hω hz) (add_le_add (I2_r2_19 hω hz) (add_le_add (I2_r2_20 hω hz)
    (I2_r2_21 hω hz))))))))))))
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by norm_num)))
  rfl

/-- The thirteen `I₂` bounds of row 4 summed. -/
theorem I2_sum_row3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∑ j, I2 ω (tableParams 3) j ≤ (32262113/1000000000 : ℝ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  have := add_le_add (I2_r3_9 hω hz) (add_le_add (I2_r3_10 hω hz) (add_le_add (I2_r3_11 hω hz)
    (add_le_add (I2_r3_12 hω hz) (add_le_add (I2_r3_13 hω hz) (add_le_add (I2_r3_14 hω hz)
    (add_le_add (I2_r3_15 hω hz) (add_le_add (I2_r3_16 hω hz) (add_le_add (I2_r3_17 hω hz)
    (add_le_add (I2_r3_18 hω hz) (add_le_add (I2_r3_19 hω hz) (add_le_add (I2_r3_20 hω hz)
    (I2_r3_21 hω hz))))))))))))
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by norm_num)))
  rfl

end LeanLab.ChenDoubleSieve.Burst9Psi2

