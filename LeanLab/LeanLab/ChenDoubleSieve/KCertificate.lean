import LeanLab.ChenDoubleSieve.KPanelArithmetic
import LeanLab.ChenDoubleSieve.JCertificate

/-!
# Certified K integrals for Table 1

Source: https://arxiv.org/pdf/0705.1652, page 22 and page 30.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace LeanLab.ChenDoubleSieve.Wu04KCertificate
open Wu04Integral (logLowerQ logUpperQ logLowerQ_cast logUpperQ_cast)
open Wu04Reduced (tableS tableSp)
open Wu04JCertificate (down up down_le le_up)
open Wu04Panels (KLower KUpper KWLower KWUpper)

def leftQ (i : Fin 5) : ℚ := 1 - 1 / tableS i
def rightQ (i : Fin 5) : ℚ := 1 - 1 / tableSp i
def nodeQ (i : Fin 5) (j : ℕ) : ℚ := leftQ i + j * (rightQ i - leftQ i) / 512

def wLowerQ (a b : ℚ) : ℚ := logLowerQ 16 (b/a) + logLowerQ 16 ((1-a)/(1-b))
def wUpperQ (a b : ℚ) : ℚ := logUpperQ 16 (b/a) + logUpperQ 16 ((1-a)/(1-b))
def lowerPanelQ (a b r : ℚ) : ℚ :=
  logLowerQ 16 (r*a-1) * wLowerQ a b + r/(r*b-1) *
    (logLowerQ 16 ((1-a)/(1-b)) - a*wUpperQ a b)
def upperPanelQ (a b r : ℚ) : ℚ :=
  logUpperQ 16 (r*a-1) * wUpperQ a b + r/(r*a-1) *
    (logUpperQ 16 ((1-a)/(1-b)) - a*wLowerQ a b)
def lowerCell (i : Fin 5) (j : ℕ) : ℚ := down (lowerPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i))
def upperCell (i : Fin 5) (j : ℕ) : ℚ := up (upperPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i))
def lowerK : Fin 5 → ℚ := ![1581378937/10000000000, 1059461845/10000000000,
  572347803/10000000000, 186171131/10000000000, 0]
def upperK : Fin 5 → ℚ := ![1581379614/10000000000, 1059462178/10000000000,
  572347924/10000000000, 186171153/10000000000, 0]

theorem parameters : ∀ i : Fin 5,
    0 < leftQ i ∧ leftQ i ≤ rightQ i ∧ rightQ i < 1 ∧
    0 < tableSp i ∧ 1 ≤ tableSp i * leftQ i - 1 := by decide +kernel

theorem K_sum_row0 : lowerK 0 ≤ ∑ j ∈ range 512, lowerCell 0 j ∧
    (∑ j ∈ range 512, upperCell 0 j) ≤ upperK 0 := by decide +kernel

theorem K_sum_row1 : lowerK 1 ≤ ∑ j ∈ range 512, lowerCell 1 j ∧
    (∑ j ∈ range 512, upperCell 1 j) ≤ upperK 1 := by decide +kernel

theorem K_sum_row2 : lowerK 2 ≤ ∑ j ∈ range 512, lowerCell 2 j ∧
    (∑ j ∈ range 512, upperCell 2 j) ≤ upperK 2 := by decide +kernel

theorem K_sum_row3 : lowerK 3 ≤ ∑ j ∈ range 512, lowerCell 3 j ∧
    (∑ j ∈ range 512, upperCell 3 j) ≤ upperK 3 := by decide +kernel

theorem K_sum_row4 : lowerK 4 ≤ ∑ j ∈ range 512, lowerCell 4 j ∧
    (∑ j ∈ range 512, upperCell 4 j) ≤ upperK 4 := by decide +kernel

theorem K_sum_certificate : ∀ i : Fin 5,
    lowerK i ≤ ∑ j ∈ range 512, lowerCell i j ∧
    (∑ j ∈ range 512, upperCell i j) ≤ upperK i := by
  intro i
  fin_cases i
  · exact K_sum_row0
  · exact K_sum_row1
  · exact K_sum_row2
  · exact K_sum_row3
  · exact K_sum_row4

theorem K_table_bounds (i : Fin 5) :
    (lowerK i : ℝ) ≤ (∫ t in (leftQ i : ℝ)..(rightQ i : ℝ),
      Real.log ((tableSp i : ℝ) * t - 1) / (t * (1-t))) ∧
    (∫ t in (leftQ i : ℝ)..(rightQ i : ℝ),
      Real.log ((tableSp i : ℝ) * t - 1) / (t * (1-t))) ≤ (upperK i : ℝ) := by
  let x : ℕ → ℝ := fun j => (nodeQ i j : ℝ)
  have hpar : 0 < (leftQ i : ℝ) ∧ (leftQ i : ℝ) ≤ rightQ i ∧ (rightQ i : ℝ) < 1 ∧
      0 < (tableSp i : ℝ) ∧ 1 ≤ (tableSp i : ℝ) * leftQ i - 1 := by
    exact_mod_cast parameters i
  obtain ⟨ha, hab, hb, hr, hra⟩ := hpar
  have hx (j : ℕ) : x j = (leftQ i : ℝ) + (j : ℝ) * ((rightQ i : ℝ) - leftQ i) / 512 := by
    simp [x, nodeQ]
  have hxp (j : ℕ) (hj : j < 512) :
      0 < x j ∧ x j ≤ x (j+1) ∧ x (j+1) < 1 ∧ 1 ≤ (tableSp i : ℝ)*x j-1 := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj1 : (j : ℝ)+1 ≤ 512 := by exact_mod_cast (Nat.succ_le_of_lt hj)
    have hxa : (leftQ i : ℝ) ≤ x j := by rw [hx]; nlinarith
    have hxb : x (j+1) ≤ (rightQ i : ℝ) := by rw [hx]; push_cast; nlinarith
    refine ⟨ha.trans_le hxa, ?_, hxb.trans_lt hb, ?_⟩
    · rw [hx, hx]; push_cast; nlinarith
    · nlinarith
  have hp := Wu04Panels.K_partition_arithmetic 16 512 x hr hxp
  have hcell (j : ℕ) : (lowerCell i j : ℝ) ≤ KLower 16 (x j) (x (j+1)) (tableSp i) ∧
      KUpper 16 (x j) (x (j+1)) (tableSp i) ≤ (upperCell i j : ℝ) := by
    have hl : (lowerCell i j : ℝ) ≤ (lowerPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i) : ℝ) := by
      exact_mod_cast down_le (lowerPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i))
    have hu : (upperPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i) : ℝ) ≤ (upperCell i j : ℝ) := by
      exact_mod_cast le_up (upperPanelQ (nodeQ i j) (nodeQ i (j+1)) (tableSp i))
    constructor
    · simpa [lowerPanelQ, wLowerQ, wUpperQ, KLower, KWLower, KWUpper, x] using hl
    · simpa [upperPanelQ, wLowerQ, wUpperQ, KUpper, KWLower, KWUpper, x] using hu
  have hsumL : (lowerK i : ℝ) ≤ ∑ j ∈ range 512, (lowerCell i j : ℝ) := by
    exact_mod_cast (K_sum_certificate i).1
  have hsumU : (∑ j ∈ range 512, (upperCell i j : ℝ)) ≤ (upperK i : ℝ) := by
    exact_mod_cast (K_sum_certificate i).2
  have hx0 : x 0 = (leftQ i : ℝ) := by rw [hx]; norm_num
  have hx512 : x 512 = (rightQ i : ℝ) := by rw [hx]; ring
  rw [hx0, hx512] at hp
  exact ⟨hsumL.trans ((sum_le_sum (fun j hj => (hcell j).1)).trans hp.1),
    hp.2.trans ((sum_le_sum (fun j hj => (hcell j).2)).trans hsumU)⟩

end LeanLab.ChenDoubleSieve.Wu04KCertificate

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.parameters

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_row0

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_row1

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_row2

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_row3

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_row4

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_sum_certificate

#print axioms LeanLab.ChenDoubleSieve.Wu04KCertificate.K_table_bounds
