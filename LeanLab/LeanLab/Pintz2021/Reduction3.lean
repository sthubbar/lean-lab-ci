/-
P0054 J. Pintz 2021, Section 3: Theorem 3 from Lemma 1 and the major arc output only.
Unit U-6771, session 20261020T2317Z-cloud53.

* `coef_S_sq`: orthogonality, `R(m) = ∫ S(β)² e(-mβ) dβ = ∑_{n₁+n₂=m} a(n₁) a(n₂)`, (1.6).
* `goldbach_of_re_pos`: for `a = aS` of (1.1), `Re R(m) > 0` makes `m` a sum of two primes.
* `R1_add_R2`: `R = R₁ + R₂` for any measurable split, (1.7).
* `section3Input_of_major`: `Section3MajorInput ε`, Lemma 1 on the minor arcs plus the major arc
  output of (3.5), (3.6) with Theorem 2 and Case 1, implies `Section3Input ε`. So
  `theorem3_of_major`: Theorem 3 is CONDITIONAL ON Lemma 1 and the major arc analysis only;
  (1.6), (1.7) and (3.1) are now proved.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.MinorArcs
import LeanLab.Pintz2021.Applications

namespace LeanLab.Pintz2021.Reduction3

open Complex Finset MeasureTheory Real
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.Pintz2021.MinorArcs

/-- `R(m) = ∑_{n₁ + n₂ = m} a(n₁) a(n₂)`, by `∫_{-1/2}^{1/2} e(kβ) dβ = [k = 0]`. -/
theorem coef_S_sq (a : ℕ → ℂ) (K m : ℕ) :
    coef (fun β => (∑ n ∈ range K, a n * e (n * β)) ^ 2) m =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K, if n1 + n2 = m then a n1 * a n2 else 0 := by
  unfold coef
  have hpt : ∀ β : ℝ, (∑ n ∈ range K, a n * e (n * β)) ^ 2 * e (-(m * β)) =
      ∑ n1 ∈ range K, ∑ n2 ∈ range K,
        a n1 * a n2 * e ((((n1 : ℤ) + n2 - m : ℤ) : ℝ) * β) := by
    intro β
    rw [sq, sum_mul_sum, sum_mul]
    refine sum_congr rfl fun n1 _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun n2 _ => ?_
    have : e ((((n1 : ℤ) + n2 - m : ℤ) : ℝ) * β) = e (n1 * β) * e (n2 * β) * e (-(m * β)) := by
      rw [← e_add, ← e_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hpt]
  have hc : ∀ (n1 n2 : ℕ), Continuous fun β : ℝ =>
      a n1 * a n2 * e ((((n1 : ℤ) + n2 - m : ℤ) : ℝ) * β) :=
    fun n1 n2 => continuous_const.mul (continuous_e_mul _)
  rw [intervalIntegral.integral_finsetSum fun n1 _ =>
    (continuous_finsetSum _ fun n2 _ => hc n1 n2).intervalIntegrable _ _]
  refine sum_congr rfl fun n1 _ => ?_
  rw [intervalIntegral.integral_finsetSum fun n2 _ => (hc n1 n2).intervalIntegrable _ _]
  refine sum_congr rfl fun n2 _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_e_int]
  by_cases h : n1 + n2 = m
  · have : ((n1 : ℤ) + n2 - m : ℤ) = 0 := by omega
    simp [h, this]
  · have : ((n1 : ℤ) + n2 - m : ℤ) ≠ 0 := by omega
    simp [h, this]

/-- (1.6): if `Re R(m) > 0` then `m = p + p'` with `p, p' ∈ (X₁, X]` prime. -/
theorem goldbach_of_re_pos (X1 X : ℝ) (m : ℕ)
    (h : 0 < (coef (fun β => S X1 X β ^ 2) m).re) : IsGoldbachSum m := by
  by_contra hng
  have hzero : coef (fun β => S X1 X β ^ 2) m = 0 := by
    unfold S
    rw [coef_S_sq]
    refine sum_eq_zero fun n1 _ => sum_eq_zero fun n2 _ => ?_
    split_ifs with hs
    · by_contra hne
      have h1 : aS X1 X n1 ≠ 0 := left_ne_zero_of_mul hne
      have h2 : aS X1 X n2 ≠ 0 := right_ne_zero_of_mul hne
      have hp1 : n1.Prime := by
        by_contra hp; exact h1 (by unfold aS; simp [hp])
      have hp2 : n2.Prime := by
        by_contra hp; exact h2 (by unfold aS; simp [hp])
      exact hng ⟨n1, n2, hp1, hp2, hs⟩
    · rfl
  rw [hzero, Complex.zero_re] at h
  exact lt_irrefl _ h

/-- The major arc part, (1.8): `R₁(m) = ∫_{[-1/2,1/2] \ mi} S(β)² e(-mβ) dβ`. -/
noncomputable def R1 (S : ℝ → ℂ) (mi : Set ℝ) (m : ℕ) : ℂ :=
  coef (miᶜ.indicator fun β => S β ^ 2) m

/-- (1.7): `R(m) = R₁(m) + R₂(m)` for any measurable `mi`. -/
theorem R1_add_R2 (S : ℝ → ℂ) (hS : Continuous S) (mi : Set ℝ) (hmi : MeasurableSet mi)
    (m : ℕ) : R1 S mi m + R2 S mi m = coef (fun β => S β ^ 2) m := by
  unfold R1 R2 coef
  have hS2 : IntervalIntegrable (fun β => S β ^ 2) volume (-(1 / 2)) (1 / 2) :=
    (hS.pow 2).intervalIntegrable _ _
  have hem : ContinuousOn (fun β : ℝ => e (-(m * β))) (Set.uIcc (-(1 / 2)) (1 / 2)) :=
    (by simpa [neg_mul] using continuous_e_mul (-(m : ℝ)) : Continuous fun β : ℝ =>
      e (-(m * β))).continuousOn
  have hi1 : IntervalIntegrable (fun β => miᶜ.indicator (fun β => S β ^ 2) β * e (-(m * β)))
      volume (-(1 / 2)) (1 / 2) :=
    IntervalIntegrable.mul_continuousOn
      ⟨hS2.1.indicator hmi.compl, hS2.2.indicator hmi.compl⟩ hem
  have hi2 : IntervalIntegrable (fun β => mi.indicator (fun β => S β ^ 2) β * e (-(m * β)))
      volume (-(1 / 2)) (1 / 2) :=
    IntervalIntegrable.mul_continuousOn ⟨hS2.1.indicator hmi, hS2.2.indicator hmi⟩ hem
  rw [← intervalIntegral.integral_add hi1 hi2]
  congr 1; ext β
  rw [← add_mul]; congr 1
  by_cases hβ : β ∈ mi
  · simp [Set.indicator_of_mem hβ, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hβ)]
  · simp [Set.indicator_of_notMem hβ, Set.indicator_of_mem (Set.mem_compl hβ)]

theorem continuous_S (X1 X : ℝ) : Continuous (S X1 X) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_e_mul _)

/-- The inputs of Section 3 that remain: for every block `Y > Y₀` some `X₁` and a measurable
set of minor arcs `mi` with Lemma 1, (1.10), at `P = Y^{7/25}`, and the major arc output of (3.5),
(3.6) with Theorem 2 and Case 1, for `R₁` the integral over the complement of `mi`. -/
def Section3MajorInput (ε : ℝ) : Prop :=
  ∃ (A : ℝ) (C M Y0 : ℕ), 0 ≤ A ∧ 0 < C ∧ ∀ Y : ℕ, Y0 < Y → ∃ (X1 : ℝ) (mi : Set ℝ)
    (𝓡 : Finset ℕ), MeasurableSet mi ∧ Lemma1On A X1 Y ((Y : ℝ) ^ (7 / 25 : ℝ)) mi ∧
    (∀ m ∈ Ioc (Y / 2) Y, Even m → (R1 (S X1 Y) mi m).re ≤ (Y : ℝ) ^ (1 - ε) →
      ∃ R0 ∈ 𝓡, R0 ∣ C * m) ∧
    (∀ R0 ∈ 𝓡, (Y : ℝ) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

/-- `Section3MajorInput ε` implies `Section3Input ε`: (1.6), (1.7) and (3.1) are proved. -/
theorem section3Input_of_major {ε : ℝ} (h : Section3MajorInput ε) :
    Applications.Section3Input ε := by
  obtain ⟨A, C, M, Y0, hA, hC, hin⟩ := h
  refine ⟨8 * A ^ 2, 10, C, M, Y0, hC, fun Y hY => ?_⟩
  obtain ⟨X1, mi, 𝓡, hmi, hL1, hMa, hP, hM⟩ := hin Y hY
  refine ⟨R1 (S X1 Y) mi, R2 (S X1 Y) mi, 𝓡, ?_, ?_, hMa, hP, hM⟩
  · intro m _ _ hpos
    rw [R1_add_R2 _ (continuous_S X1 Y) mi hmi] at hpos
    exact goldbach_of_re_pos X1 Y m hpos
  · have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
    have hsub : Ioc (Y / 2) Y ⊆ range (Y + 1) := by
      intro m hm; rw [mem_range]; have := (mem_Ioc.mp hm).2; omega
    calc ∑ m ∈ Ioc (Y / 2) Y, ‖R2 (S X1 Y) mi m‖ ^ 2
        ≤ ∑ m ∈ range (Y + 1), ‖R2 (S X1 Y) mi m‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ ≤ _ := minor31_of_lemma1 hA hY1 mi hmi hL1 (Y + 1)

/-- CONDITIONAL ON Lemma 1 and the major arc output, `Section3MajorInput ε` for every `ε > 0`:
Theorem 3, `E(X) ≪_ε X^{0.72+ε}`. -/
theorem theorem3_of_major (h : ∀ ε : ℝ, 0 < ε → Section3MajorInput ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem3 :=
  Applications.theorem3_of_section3Input fun ε hε => section3Input_of_major (h ε hε)

end LeanLab.Pintz2021.Reduction3

#print axioms LeanLab.Pintz2021.Reduction3.coef_S_sq
#print axioms LeanLab.Pintz2021.Reduction3.goldbach_of_re_pos
#print axioms LeanLab.Pintz2021.Reduction3.R1_add_R2
#print axioms LeanLab.Pintz2021.Reduction3.section3Input_of_major
#print axioms LeanLab.Pintz2021.Reduction3.theorem3_of_major

