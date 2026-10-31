/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 pages 6 to 8, displays A to J and Table 1.
The asymptotic claims are definitions of Props. None is asserted as a theorem here.
-/
import LeanLab.PlattTrudgian2014.Table1

namespace LeanLab.PlattTrudgian2014

noncomputable def primePowerPart (degrees : List ℕ) (p : Fin degrees.length → ℕ) : ℕ :=
  ∑ i, p i ^ degrees.get i

def twoPowerPart (ν : List ℕ) : ℕ := (ν.map fun j => 2 ^ j).sum

def WaringRep (degrees : List ℕ) (K N : ℕ) : Prop :=
  ∃ p : Fin degrees.length → ℕ, (∀ i, Nat.Prime (p i)) ∧
    ∃ ν : List ℕ, (∀ j ∈ ν, 0 < j) ∧ ν.length ≤ K ∧
      N = primePowerPart degrees p + twoPowerPart ν

def SharedWaringRep (degrees : List ℕ) (K B1 B2 : ℕ) : Prop :=
  ∃ p q : Fin degrees.length → ℕ, (∀ i, Nat.Prime (p i)) ∧ (∀ i, Nat.Prime (q i)) ∧
    ∃ ν : List ℕ, (∀ j ∈ ν, 0 < j) ∧ ν.length ≤ K ∧
      B1 = primePowerPart degrees p + twoPowerPart ν ∧
      B2 = primePowerPart degrees q + twoPowerPart ν

def WaringApprox (degrees : List ℕ) (parity K : ℕ) : Prop :=
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → N % 2 = parity → WaringRep degrees K N

def SharedWaringApprox (degrees : List ℕ) (parity K : ℕ) : Prop :=
  ∃ N0 : ℕ, ∀ B1 B2 : ℕ, N0 ≤ B2 → B2 < B1 →
    B1 % 2 = parity → B2 % 2 = parity → SharedWaringRep degrees K B1 B2

/-- The same open strip definition used in LeanLab.DERZ1997, copied to avoid cited theorem imports. -/
def WaringGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

def ClaimA : Prop := WaringApprox [2, 2, 2, 2] 0 45
def ClaimB : Prop := WaringApprox [1, 2, 2] 1 34
def ClaimC : Prop := WaringApprox [3, 3, 3, 3, 3, 3, 3, 3] 0 330
def ClaimD : Prop := WaringApprox [1, 3, 3, 3, 3] 1 102
def ClaimE : Prop := WaringApprox [2, 2, 3, 3, 3, 3] 0 205
def ClaimF : Prop := WaringApprox [1, 2, 3, 3] 0 156
def ClaimG : Prop := SharedWaringApprox [1, 1] 0 62
def ClaimG_GRH : Prop := WaringGRH → SharedWaringApprox [1, 1] 0 31
def ClaimH : Prop := SharedWaringApprox [2, 2, 2, 2] 0 138
def ClaimI : Prop := SharedWaringApprox [3, 3, 3, 3, 3, 3, 3, 3] 0 1319
def ClaimJ : Prop := SharedWaringApprox [1, 2, 2] 1 323

theorem WaringRep_mono {degrees : List ℕ} {K K' N : ℕ} (hK : K ≤ K')
    (h : WaringRep degrees K N) : WaringRep degrees K' N := by
  obtain ⟨p, hp, ν, hν, hn, heq⟩ := h
  exact ⟨p, hp, ν, hν, hn.trans hK, heq⟩

theorem SharedWaringRep_mono {degrees : List ℕ} {K K' B1 B2 : ℕ} (hK : K ≤ K')
    (h : SharedWaringRep degrees K B1 B2) : SharedWaringRep degrees K' B1 B2 := by
  obtain ⟨p, q, hp, hq, ν, hν, hn, heq1, heq2⟩ := h
  exact ⟨p, q, hp, hq, ν, hν, hn.trans hK, heq1, heq2⟩

theorem WaringRep_empty (degrees : List ℕ) (p : Fin degrees.length → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (K : ℕ) : WaringRep degrees K (primePowerPart degrees p) := by
  refine ⟨p, hp, [], by simp, by simp, ?_⟩
  simp [twoPowerPart]

theorem SharedWaringRep_empty (degrees : List ℕ) (p q : Fin degrees.length → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hq : ∀ i, Nat.Prime (q i)) (K : ℕ) :
    SharedWaringRep degrees K (primePowerPart degrees p) (primePowerPart degrees q) := by
  refine ⟨p, q, hp, hq, [], by simp, by simp, ?_, ?_⟩ <;> simp [twoPowerPart]

theorem WaringRep_A_instance : WaringRep [2, 2, 2, 2] 0 16 := by
  convert WaringRep_empty [2, 2, 2, 2] (fun _ => 2) (fun _ => by decide) 0 using 1 <;>
    norm_num [primePowerPart, Fin.sum_univ_succ]

theorem SharedWaringRep_J_instance : SharedWaringRep [1, 2, 2] 0 21 11 := by
  convert SharedWaringRep_empty [1, 2, 2] (fun _ => 3)
    (fun i => if i = 0 then 3 else 2)
    (fun _ => by decide) (fun i => by split_ifs <;> decide) 0 using 1 <;>
    norm_num [primePowerPart, Fin.sum_univ_succ]
  all_goals decide +kernel

#print axioms WaringRep_mono
#print axioms SharedWaringRep_mono
#print axioms WaringRep_empty
#print axioms SharedWaringRep_empty
#print axioms WaringRep_A_instance
#print axioms SharedWaringRep_J_instance

end LeanLab.PlattTrudgian2014
