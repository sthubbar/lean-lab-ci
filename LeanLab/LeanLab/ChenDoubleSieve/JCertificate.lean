import LeanLab.ChenDoubleSieve.JPanelArithmetic
import LeanLab.ChenDoubleSieve.ReducedCertificate

/-!
# Exact rational certificates for the five J integrals

Source: https://arxiv.org/pdf/0705.1652, page 22 and page 30, Table 1 rows 5 to 9.
Each row uses 512 panels and sixteen logarithm terms with explicit remainders.
AI wrote the Lean code. Binary Goldbach is open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04JCertificate
open Wu04Integral (logLowerQ logUpperQ logLowerQ_cast logUpperQ_cast)
open Wu04Reduced (tableSp)
open Wu04Panels (JLower JUpper)

/-- Directed rounding to fifteen decimal places. -/
def down (q : ℚ) : ℚ := (⌊q * 1000000000000000⌋ : ℚ) / 1000000000000000
def up (q : ℚ) : ℚ := (⌈q * 1000000000000000⌉ : ℚ) / 1000000000000000

theorem down_le (q : ℚ) : down q ≤ q := by
  unfold down
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

theorem le_up (q : ℚ) : q ≤ up q := by
  unfold up
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

/-- Uniform rational partition for each printed J endpoint. -/
def nodeQ (i : Fin 5) (j : ℕ) : ℚ := 2 + j * (tableSp i - 3) / 512

/-- Rational versions of the proved panel expressions. -/
def lowerPanelQ (a b : ℚ) : ℚ :=
  logLowerQ 16 (a - 1) * logLowerQ 16 (b / a) +
    ((b - a) - a * logUpperQ 16 (b / a)) / (b - 1)
def upperPanelQ (a b : ℚ) : ℚ :=
  logUpperQ 16 (a - 1) * logUpperQ 16 (b / a) +
    ((b - a) - a * logLowerQ 16 (b / a)) / (a - 1)

def lowerCell (i : Fin 5) (j : ℕ) : ℚ := down (lowerPanelQ (nodeQ i j) (nodeQ i (j + 1)))
def upperCell (i : Fin 5) (j : ℕ) : ℚ := up (upperPanelQ (nodeQ i j) (nodeQ i (j + 1)))

/-- Final interval endpoints at scale ten billion. -/
def lowerJ : Fin 5 → ℚ := ![602029557/10000000000, 418370265/10000000000,
  234940293/10000000000, 80029211/10000000000, 0]
def upperJ : Fin 5 → ℚ := ![602030612/10000000000, 418370879/10000000000,
  234940554/10000000000, 80029265/10000000000, 0]

/-- Every parameter endpoint is at least three. -/
theorem parameters : ∀ i : Fin 5, (3 : ℚ) ≤ tableSp i := by decide +kernel

/-- Exact rounded panel certificate for Table 1 J row 5. -/
theorem J_sum_row0 :
    lowerJ 0 ≤ ∑ j ∈ range 512, lowerCell 0 j ∧
    (∑ j ∈ range 512, upperCell 0 j) ≤ upperJ 0 := by
  decide +kernel

/-- Exact rounded panel certificate for Table 1 J row 6. -/
theorem J_sum_row1 :
    lowerJ 1 ≤ ∑ j ∈ range 512, lowerCell 1 j ∧
    (∑ j ∈ range 512, upperCell 1 j) ≤ upperJ 1 := by
  decide +kernel

/-- Exact rounded panel certificate for Table 1 J row 7. -/
theorem J_sum_row2 :
    lowerJ 2 ≤ ∑ j ∈ range 512, lowerCell 2 j ∧
    (∑ j ∈ range 512, upperCell 2 j) ≤ upperJ 2 := by
  decide +kernel

/-- Exact rounded panel certificate for Table 1 J row 8. -/
theorem J_sum_row3 :
    lowerJ 3 ≤ ∑ j ∈ range 512, lowerCell 3 j ∧
    (∑ j ∈ range 512, upperCell 3 j) ≤ upperJ 3 := by
  decide +kernel

/-- Exact rounded panel certificate for Table 1 J row 9. -/
theorem J_sum_row4 :
    lowerJ 4 ≤ ∑ j ∈ range 512, lowerCell 4 j ∧
    (∑ j ∈ range 512, upperCell 4 j) ≤ upperJ 4 := by
  decide +kernel

/-- Combine the five bounded memory row certificates. -/
theorem J_sum_certificate : ∀ i : Fin 5,
    lowerJ i ≤ ∑ j ∈ range 512, lowerCell i j ∧
    (∑ j ∈ range 512, upperCell i j) ≤ upperJ i := by
  intro i
  fin_cases i
  · exact J_sum_row0
  · exact J_sum_row1
  · exact J_sum_row2
  · exact J_sum_row3
  · exact J_sum_row4

/-- Rigorous bounds for the five actual J integrals. -/
theorem J_table_bounds (i : Fin 5) :
    (lowerJ i : ℝ) ≤ (∫ t in (2 : ℝ)..((tableSp i : ℝ) - 1), Real.log (t - 1) / t) ∧
    (∫ t in (2 : ℝ)..((tableSp i : ℝ) - 1), Real.log (t - 1) / t) ≤ (upperJ i : ℝ) := by
  let x : ℕ → ℝ := fun j => (nodeQ i j : ℝ)
  have hsp : (3 : ℝ) ≤ tableSp i := by exact_mod_cast parameters i
  have hx (j : ℕ) : x j = 2 + (j : ℝ) * ((tableSp i : ℝ) - 3) / 512 := by simp [x, nodeQ]
  have hxp (j : ℕ) : 2 ≤ x j ∧ x j ≤ x (j + 1) := by
    rw [hx j, hx (j + 1)]
    push_cast
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hp : 0 ≤ (j : ℝ) * ((tableSp i : ℝ) - 3) := mul_nonneg hn (by linarith)
    constructor <;> nlinarith
  have hp := Wu04Panels.J_partition_arithmetic 16 512 x (fun j hj => hxp j)
  have hcell (j : ℕ) : (lowerCell i j : ℝ) ≤ JLower 16 (x j) (x (j + 1)) ∧
      JUpper 16 (x j) (x (j + 1)) ≤ (upperCell i j : ℝ) := by
    have hl : (lowerCell i j : ℝ) ≤ (lowerPanelQ (nodeQ i j) (nodeQ i (j + 1)) : ℝ) := by
      exact_mod_cast down_le (lowerPanelQ (nodeQ i j) (nodeQ i (j + 1)))
    have hu : (upperPanelQ (nodeQ i j) (nodeQ i (j + 1)) : ℝ) ≤ (upperCell i j : ℝ) := by
      exact_mod_cast le_up (upperPanelQ (nodeQ i j) (nodeQ i (j + 1)))
    constructor
    · simpa [lowerPanelQ, JLower, x] using hl
    · simpa [upperPanelQ, JUpper, x] using hu
  have hsumL : (lowerJ i : ℝ) ≤ ∑ j ∈ range 512, (lowerCell i j : ℝ) := by
    exact_mod_cast (J_sum_certificate i).1
  have hsumU : (∑ j ∈ range 512, (upperCell i j : ℝ)) ≤ (upperJ i : ℝ) := by
    exact_mod_cast (J_sum_certificate i).2
  have hx0 : x 0 = 2 := by rw [hx]; norm_num
  have hx512 : x 512 = (tableSp i : ℝ) - 1 := by rw [hx]; ring
  rw [hx0, hx512] at hp
  exact ⟨hsumL.trans ((sum_le_sum (fun j hj => (hcell j).1)).trans hp.1),
    hp.2.trans ((sum_le_sum (fun j hj => (hcell j).2)).trans hsumU)⟩

end LeanLab.ChenDoubleSieve.Wu04JCertificate

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.down_le
#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.le_up
#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.parameters
#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_certificate
#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_table_bounds

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_row0

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_row1

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_row2

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_row3

#print axioms LeanLab.ChenDoubleSieve.Wu04JCertificate.J_sum_row4
