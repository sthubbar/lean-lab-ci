/-
AI wrote this Lean code for CODEX task70.
All admissible nonmaximum single replacements before target 450.
Section 2, equation 2.3, page 427, and Table I, page 430.
-/
import LeanLab.SteinStein1965.Choice450

namespace LeanLab.SteinStein1965

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def insertDesc (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: bs => if b ≤ a then a :: b :: bs else b :: insertDesc a bs

def sortDesc (xs : List ℕ) : List ℕ := xs.foldr insertDesc []

theorem mem_insertDesc (a b : ℕ) (xs : List ℕ) :
    b ∈ insertDesc a xs ↔ b = a ∨ b ∈ xs := by
  induction xs with
  | nil => simp [insertDesc]
  | cons x xs ih =>
    simp only [insertDesc]
    split <;> simp [ih, or_assoc, or_left_comm]

theorem mem_sortDesc (a : ℕ) (xs : List ℕ) : a ∈ sortDesc xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [sortDesc]
  | cons x xs ih =>
    change a ∈ insertDesc x (sortDesc xs) ↔ a ∈ x :: xs
    rw [mem_insertDesc, List.mem_cons, ih]

def choiceScanStep (st : (List ℕ × List ℕ) × List (ℕ × ℕ)) (m : ℕ) :
    (List ℕ × List ℕ) × List (ℕ × ℕ) :=
  let bs := st.1.1
  let choices := if covers bs m then [] else
    ((sortDesc (cands (primeA 89) bs m)).filter
      (fun a => a != (cands (primeA 89) bs m).max?.getD 0)).map (fun a => (m, a))
  (step (primeA 89) st.1 m, st.2 ++ choices)

def trackChoices89 (N : ℕ) : (List ℕ × List ℕ) × List (ℕ × ℕ) :=
  (evensIn 178 N).foldl choiceScanStep (([89, 97], []), [])

theorem choiceScan_state (L : List ℕ) (st : (List ℕ × List ℕ) × List (ℕ × ℕ)) :
    (L.foldl choiceScanStep st).1 = L.foldl (step (primeA 89)) st.1 := by
  induction L generalizing st with
  | nil => rfl
  | cons m L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    rfl

theorem trackChoices89_state (N : ℕ) : (trackChoices89 N).1 = sPrime 89 N :=
  choiceScan_state _ _

def earlierOptions89 : List (ℕ × ℕ) := (trackChoices89 448).2

theorem earlierOptions89_eq : earlierOptions89 =
    [(220, 113), (250, 137), (260, 157), (260, 151), (268, 167), (268, 137), (274, 167), (284, 157), (296, 193), (296, 157), (314, 151), (316, 167), (316, 137), (332, 223), (332, 193), (332, 151), (364, 257), (364, 251), (364, 233), (364, 191), (364, 137), (382, 281), (382, 269), (382, 251), (382, 233), (386, 277), (386, 223), (386, 157), (388, 257), (388, 239), (404, 277), (404, 241), (404, 223), (404, 193), (418, 311), (418, 269), (418, 239), (418, 191), (418, 137)] := by
  unfold earlierOptions89 trackChoices89 choiceScanStep
  decide +kernel

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.earlierOptions89_eq

#print axioms LeanLab.SteinStein1965.choiceScan_state
#print axioms LeanLab.SteinStein1965.trackChoices89_state

#print axioms LeanLab.SteinStein1965.mem_insertDesc
#print axioms LeanLab.SteinStein1965.mem_sortDesc
