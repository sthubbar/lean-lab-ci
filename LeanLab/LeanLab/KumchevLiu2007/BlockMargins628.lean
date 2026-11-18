/-
Parameter certificates for the repaired Decomp516a block route.
The initial Gallagher interval is completely elementary on these blocks.
The remaining bulk leaf has a verified positive margin above Y to two thirds.
Sources are P0088 page 8 after display 31 and page 15 before display 53.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628

namespace LeanLab.KumchevLiu2007.Task628

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology

/-- Page 8 after display 31, uniform derived initial interval theorem.
For every positive A choose B0 equal to A plus two. For each B above B0
and positive epsilon, all sufficiently large X have the initial energy
bound with constant four throughout the repaired block range, for every
frequency. No analytic cancellation input is used. -/
theorem initial_energy_on_blocks (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H α : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            4 * H ^ 2 / Real.log X ^ (A + 2) := by
  refine ⟨A + 2, by positivity, ?_⟩
  intro B hB ε hε
  obtain ⟨X0, hX0, hr⟩ := block_root_eventually B ε hε
  refine ⟨X0, by linarith, ?_⟩
  intro X H α hX hlo hhi
  have hX3 : 3 ≤ X := hX0.trans hX
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  exact block_initial_energy hX3 hY (hr X H hX hlo) (by linarith) hhi

/-- Page 15, the theta2 condition in the Lemma 3.4 application.
Every positive epsilon admits a positive auxiliary eta at most one
hundredth for which the Y exponent times two thirds plus eta leaves the
explicit positive gap five epsilon over twelve below the final X exponent.
This permits a separate small parameter in the source cutoffs. -/
theorem bulk_power_margin (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 100 ∧
      (7 / 12 + ε / 2) * (2 / 3 + η) ≤ 7 / 18 + 7 * ε / 12 := by
  have hθ : 0 < 7 / 12 + ε / 2 := by linarith
  let η := min (1 / 100 : ℝ) (ε / (4 * (7 / 12 + ε / 2)))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hm : (7 / 12 + ε / 2) * η ≤ ε / 4 := by
    calc _ ≤ (7 / 12 + ε / 2) * (ε / (4 * (7 / 12 + ε / 2))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hθ.le
      _ = _ := by field_simp
  refine ⟨η, hη, min_le_left _ _, ?_⟩
  nlinarith

/-- Page 15, derived block form of the theta2 lower range.
For fixed B and positive epsilon one can choose a positive eta at most
one hundredth so that every repaired block eventually has H at least
Y to two thirds plus eta. Four logarithmic powers are absorbed in the
strict positive power margin. This proves a parameter condition only.
The bulk analytic estimate remains a separate leaf. -/
theorem bulk_range_eventually (B ε : ℝ) (hε : 0 < ε) :
    ∃ η X0 : ℝ, 0 < η ∧ η ≤ 1 / 100 ∧ 3 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        windowY X ε ^ (2 / 3 + η) ≤ H := by
  obtain ⟨η, hη, hηhi, hm⟩ := bulk_power_margin ε hε
  have hd : 0 < 5 * ε / 12 := by positivity
  have ht := (isLittleO_log_rpow_rpow_atTop (4 * B) hd).bound one_pos
  obtain ⟨X0, ht⟩ := Filter.eventually_atTop.mp ht
  refine ⟨η, max 3 X0, hη, hηhi, le_max_left _ _, ?_⟩
  intro X H hX hH
  have hX3 : 3 ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL _
  have h := ht X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hL.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hX0.le _)] at h
  have he : (Real.log X ^ B) ^ (4 : ℕ) = Real.log X ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    norm_num
    ring
  refine le_trans ?_ hH
  rw [windowY, ← Real.rpow_mul hX0.le, zpow_neg, zpow_ofNat,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos hP 4), he]
  calc
    _ ≤ X ^ ((7 / 12 + ε / 2) * (2 / 3 + η)) * X ^ (5 * ε / 12) := by gcongr
    _ = X ^ ((7 / 12 + ε / 2) * (2 / 3 + η) + 5 * ε / 12) :=
      (Real.rpow_add hX0 _ _).symm
    _ ≤ X ^ (7 / 18 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)

example : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 100 ∧
    (7 / 12 + (1 / 10 : ℝ) / 2) * (2 / 3 + η) ≤ 7 / 18 + 7 * (1 / 10 : ℝ) / 12 :=
  bulk_power_margin (1 / 10) (by norm_num)

example : ∃ η X0 : ℝ, 0 < η ∧ η ≤ 1 / 100 ∧ 3 ≤ X0 ∧ ∀ X H : ℝ,
    X0 ≤ X → X ^ (7 / 18 + (1 / 10 : ℝ)) * (Real.log X ^ (1 : ℝ)) ^ (-4 : ℤ) ≤ H →
      windowY X (1 / 10) ^ (2 / 3 + η) ≤ H :=
  bulk_range_eventually 1 (1 / 10) (by norm_num)

example : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H α : ℝ, X0 ≤ X →
      X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
      H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
      (∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          4 * H ^ 2 / Real.log X ^ ((1 : ℝ) + 2) :=
  initial_energy_on_blocks 1 one_pos

end LeanLab.KumchevLiu2007.Task628

#print axioms LeanLab.KumchevLiu2007.Task628.initial_energy_on_blocks
#print axioms LeanLab.KumchevLiu2007.Task628.bulk_power_margin
#print axioms LeanLab.KumchevLiu2007.Task628.bulk_range_eventually
