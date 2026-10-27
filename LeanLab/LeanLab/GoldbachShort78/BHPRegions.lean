import LeanLab.GoldbachShort78.BHPBookkeeping

/-!
AI wrote the Lean code, Codex task57. Binary Goldbach is OPEN.
BHP 2001, the displayed polygons on pp. 559 and 560.
https://doi.org/10.1112/plms/83.3.532
Only the displayed closed inequalities are represented here.
No disjointness or analytic sieve identity is asserted.
-/

namespace LeanLab.GoldbachShort78

/-- The displayed inequalities for polygon A on p. 559. -/
def bhpRegionA (θ a b : ℝ) : Prop :=
  1 / 4 ≤ a ∧ a ≤ 2 / 5 ∧ (1 - a) / 3 ≤ b ∧
    b ≤ a ∧ b ≤ (3 * θ - 1) / 2 ∧ b ≤ 1 - 2 * a

/-- The displayed inequalities for polygon B on p. 559. -/
def bhpRegionB (θ a b : ℝ) : Prop :=
  (3 - 3 * θ) / 4 ≤ a ∧ a ≤ 1 / 2 ∧ a / 2 ≤ b ∧
    1 - 2 * a ≤ b ∧ b ≤ (3 * θ - 1) / 2 ∧ b ≤ (1 - a) / 2

/-- The A and B symmetry printed on p. 560, with theta left as a parameter. -/
theorem bhp_regionA_iff_B (θ a b : ℝ) :
    bhpRegionA θ a b ↔ bhpRegionB θ (1 - a - b) b := by
  simp only [bhpRegionA, bhpRegionB]
  constructor
  · rintro ⟨ha0, ha1, hb0, hb1, hb2, hb3⟩
    refine ⟨?_, ?_, ?_, ?_, hb2, ?_⟩ <;> linarith
  · rintro ⟨ha0, ha1, hb0, hb1, hb2, hb3⟩
    refine ⟨?_, ?_, ?_, ?_, hb2, ?_⟩ <;> linarith

/-- The displayed inequalities for polygon E on p. 560. -/
def bhpRegionE (θ a b : ℝ) : Prop :=
  (3 * θ - 1) / 2 ≤ a ∧ a ≤ (3 - 3 * θ) / 4 ∧
    (3 * θ - 1) / 2 ≤ b ∧ b ≤ a ∧ b ≤ 1 - 2 * a

/-- The displayed inequalities for polygon F on p. 560. -/
def bhpRegionF (θ a b : ℝ) : Prop :=
  1 / 3 ≤ a ∧ a ≤ 2 - 3 * θ ∧ 1 - 2 * a ≤ b ∧
    (3 * θ - 1) / 2 ≤ b ∧ b ≤ (1 - a) / 2

/-- The analogous E and F symmetry stated on p. 560. -/
theorem bhp_regionE_iff_F (θ a b : ℝ) :
    bhpRegionE θ a b ↔ bhpRegionF θ (1 - a - b) b := by
  simp only [bhpRegionE, bhpRegionF]
  constructor
  · rintro ⟨ha0, ha1, hb0, hb1, hb2⟩
    refine ⟨?_, ?_, ?_, hb0, ?_⟩ <;> linarith
  · rintro ⟨ha0, ha1, hb0, hb1, hb2⟩
    refine ⟨?_, ?_, hb1, ?_, ?_⟩ <;> linarith

end LeanLab.GoldbachShort78
