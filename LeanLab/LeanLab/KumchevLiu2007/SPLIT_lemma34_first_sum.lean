/-
Split of `lemma34_first_sum` of `LeanLab.KumchevLiu2007.Eq33RouteD`, the mean
square of the first sum of the Buchstab decomposition on the window of length
Y, under the minor arc hypothesis on alpha.

The estimate is cut on the two axes that it really has:

* the size of the sieve cut-off z. Below two the rough weight is identically
  one, since the smallest prime factor is two; above two the weight is the
  rough indicator. These are the two regimes of the statement.
* the two halves of the t window. Near Y / 4 the short sum has twice as many
  terms as near Y, so the two halves are the two different counting regimes,
  and the integral over the whole window is the sum of the two.

That gives four leaves, each the target estimate on a subset of its parameter
range: a cut-off range or an integration interval strictly smaller. No leaf
implies the target and no leaf assumes it. The assembly adds the two half
intervals and takes twice the larger of the four constants.

The H range above Y, recorded as a question in the parent file, is left inside
each leaf: every leaf keeps the whole written range of H.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import LeanLab.KumchevLiu2007.SmallCutoff674

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: the small cut-off case on the left half of the window. The sieve
cut-off is at most two, so every prime factor of a term exceeds it and the
rough weight is one; the estimate is only claimed on [Y / 4, Y / 2], where the
short sum has the larger number of terms. -/
theorem leaf_small_cutoff_left_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ 2 →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := Task674.unweighted_first_sum A hA
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hbound⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hb := hbound X H hX hH hHU α q a hcop hqP hqQ hclose
    (windowY X ε / 4) (windowY X ε / 2) (by positivity) (by linarith) (by linarith)
  simpa only [roughWeight_eq_one_of_le_two z hz, one_mul] using hb

/-- LEAF: the small cut-off case on the right half of the window. Same
trivial weight as the previous leaf, on [Y / 2, Y], where the short sum has the
smaller number of terms and the bound is the easier one. -/
theorem leaf_small_cutoff_right_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ 2 →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, h⟩ := Task674.unweighted_first_sum A hA
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X0, hC, hX0, hbound⟩ := h B hB ε hε
  refine ⟨C, X0, hC, hX0, ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hb := hbound X H hX hH hHU α q a hcop hqP hqQ hclose
    (windowY X ε / 2) (windowY X ε) (by positivity) (by linarith) (by linarith)
  simpa only [roughWeight_eq_one_of_le_two z hz, one_mul] using hb

/-- LEAF: the genuinely rough case on the left half of the window. The
cut-off is above two and at most Y^(1/6 + eps/2), so the rough weight is the
indicator of the integers all of whose prime factors reach the cut-off, and the
estimate is claimed only on [Y / 4, Y / 2]. -/
theorem leaf_large_cutoff_left_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: the genuinely rough case on the right half of the window. The same
cut-off range as the previous leaf, on [Y / 2, Y], the half where the short sum
has fewer terms. -/
theorem leaf_large_cutoff_right_half (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- The target estimate, from the four leaves: split the window at Y / 2, take
the smaller cut-off on both halves when z is at most two and the rough case on
both halves otherwise, and use twice the largest of the four constants. -/
theorem lemma34_first_sum_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := leaf_small_cutoff_left_half A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_small_cutoff_right_half A hA
  obtain ⟨B3, hB3, h3⟩ := leaf_large_cutoff_left_half A hA
  obtain ⟨B4, hB4, h4⟩ := leaf_large_cutoff_right_half A hA
  refine ⟨max B1 (max B2 (max B3 B4)), lt_of_lt_of_le hB1 (le_max_left _ _),
    fun B hB ε hε => ?_⟩
  have hB1' : B1 ≤ B := (le_max_left _ _).trans hB
  have hB2' : B2 ≤ B := ((le_max_left _ _).trans (le_max_right _ _)).trans hB
  have hB3' : B3 ≤ B :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  have hB4' : B4 ≤ B :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hB1' ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B hB2' ε hε
  obtain ⟨C3, X3, hC3, hX3, k3⟩ := h3 B hB3' ε hε
  obtain ⟨C4, X4, hC4, hX4, k4⟩ := h4 B hB4' ε hε
  have hCpos : 0 < 2 * max C1 (max C2 (max C3 C4)) := by
    have hM : 0 < max C1 (max C2 (max C3 C4)) := lt_of_lt_of_le hC1 (le_max_left _ _)
    linarith
  refine ⟨2 * max C1 (max C2 (max C3 C4)), max X1 (max X2 (max X3 X4)),
    hCpos, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHU α q a hcop hqP hqQ hclose z hz
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hXd : X4 ≤ X :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hX
  have hX1' : 1 < X := by linarith [hX1.trans hXa]
  have hL : 0 < Real.log X := Real.log_pos hX1'
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (by positivity) (Real.rpow_pos_of_pos hL A).le
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2)
      volume (windowY X ε / 4) (windowY X ε / 2) :=
    short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2)
      volume (windowY X ε / 2) (windowY X ε) :=
    short_sum_sq_intervalIntegrable (squareWindow (windowY X ε))
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  rw [(intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm]
  have hkey1 : C1 * H ^ 2 / Real.log X ^ A = C1 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey2 : C2 * H ^ 2 / Real.log X ^ A = C2 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey3 : C3 * H ^ 2 / Real.log X ^ A = C3 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkey4 : C4 * H ^ 2 / Real.log X ^ A = C4 * (H ^ 2 / Real.log X ^ A) := by ring
  have hkeyC : (2 * max C1 (max C2 (max C3 C4))) * H ^ 2 / Real.log X ^ A =
      (2 * max C1 (max C2 (max C3 C4))) * (H ^ 2 / Real.log X ^ A) := by ring
  by_cases hz2 : z ≤ 2
  · have e1 := k1 X H hXa hH hHU α q a hcop hqP hqQ hclose z hz2
    have e2 := k2 X H hXb hH hHU α q a hcop hqP hqQ hclose z hz2
    rw [hkey1] at e1
    rw [hkey2] at e2
    rw [hkeyC] at ⊢
    have hb1 : C1 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq
    have hb2 : C2 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hq
    linarith
  · have hz2' : 2 < z := not_le.mp hz2
    have e3 := k3 X H hXc hH hHU α q a hcop hqP hqQ hclose z hz2' hz
    have e4 := k4 X H hXd hH hHU α q a hcop hqP hqQ hclose z hz2' hz
    rw [hkey3] at e3
    rw [hkey4] at e4
    rw [hkeyC] at ⊢
    have hb3 : C3 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hq
    have hb4 : C4 * (H ^ 2 / Real.log X ^ A) ≤
        max C1 (max C2 (max C3 C4)) * (H ^ 2 / Real.log X ^ A) :=
      mul_le_mul_of_nonneg_right
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hq
    linarith

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_small_cutoff_left_half
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_small_cutoff_right_half
