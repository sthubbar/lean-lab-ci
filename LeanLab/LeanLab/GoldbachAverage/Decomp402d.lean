import LeanLab.GoldbachAverage.Decomp402a

/-!
Goldston and Suriajaya, arXiv 2110.14250v2 page 9 eqs. 48 and 49.
The positive window is normalized exactly by a finite floor sum.
The negative half line is a translated zero extended prefix.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp402d
open Finset MeasureTheory
open Decomp287b WeightedPrefix82 WeightedIncrement124 GallagherReduction124 I2Bound124

/-- The exponential coefficient agrees with the real weighted coefficient in GS page 9 eq. 49. -/
theorem coefficients_eq_real (N n : ℕ) :
    coefficients N n = ((Real.exp (-(n : ℝ) / N) * cfr n : ℝ) : ℂ) := by
  have he : Real.exp (-(n : ℝ) / N) = Real.exp (-(1 / (N : ℝ))) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hc : cf n = (cfr n : ℂ) := by
    unfold cf cfr
    push_cast
    split_ifs <;> simp
  rw [coefficients, hc, he]
  push_cast
  ring

/-- For a nonnegative starting point the moving sum is the finite increment, GS page 9 eq. 49. -/
theorem movingSum_eq_increment (N : ℕ) {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    movingSum (coefficients N) x h = (weightedIncrement N x h : ℂ) := by
  classical
  rw [weighted_increment_eq_sum N hh]
  push_cast
  have he (n : ℕ) : x < (n : ℝ) ∧ (n : ℝ) ≤ x + h ↔
      n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊ := by
    rw [mem_Ioc, Nat.floor_lt hx, Nat.le_floor_iff (by linarith : 0 ≤ x + h)]
  unfold movingSum
  rw [tsum_eq_sum (s := Ioc ⌊x⌋₊ ⌊x + h⌋₊) (fun n hn => by
    rw [if_neg (by simpa only [he] using hn)] )]
  apply sum_congr rfl
  intro n hn
  rw [if_pos ((he n).mpr hn), coefficients_eq_real]
  push_cast
  rfl

/-- The positive half line spatial mass is I2, GS page 9 eq. 49. -/
theorem positive_mass_eq_I2 (N : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ x : ℝ in Set.Ioi 0, ‖movingSum (coefficients N) x h‖ ^ 2) = I2 N h := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change ‖movingSum (coefficients N) x h‖ ^ 2 = weightedIncrement N x h ^ 2
  rw [movingSum_eq_increment N hx.le hh, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The weighted prefix vanishes at nonpositive cutoffs, GS page 9 negative support split. -/
theorem weightedPrefix_nonpos (N : ℕ) {u : ℝ} (hu : u ≤ 0) :
    weightedPrefix N u = 0 := by
  simp [weightedPrefix, Nat.floor_of_nonpos hu, cfr]

/-- On the negative half line the moving sum is a zero extended prefix, GS page 9. -/
theorem movingSum_eq_prefix_nonpos (N : ℕ) {x h : ℝ} (hx : x ≤ 0) :
    movingSum (coefficients N) x h = (weightedPrefix N (x + h) : ℂ) := by
  classical
  unfold movingSum weightedPrefix
  push_cast
  rw [tsum_eq_sum (s := Icc 0 ⌊x + h⌋₊) (fun n hn => by
    by_cases hn0 : n = 0
    · subst n
      simp [coefficients, cf]
    · have hu : ¬(n : ℝ) ≤ x + h := by
        intro hu
        apply hn
        exact mem_Icc.mpr ⟨Nat.zero_le _, (Nat.le_floor_iff' hn0).mpr hu⟩
      exact if_neg (fun hw => hu hw.2))]
  apply sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [coefficients, cf, cfr]
  · have hlo : x < (n : ℝ) := lt_of_le_of_lt hx (by exact_mod_cast Nat.pos_of_ne_zero hn0)
    have hup : (n : ℝ) ≤ x + h := (Nat.le_floor_iff' hn0).mp (mem_Icc.mp hn).2
    rw [if_pos ⟨hlo, hup⟩, coefficients_eq_real]
    push_cast
    rfl

/-- LEAF. GS page 9, the split immediately before eq. 48 and the definition of I1 in eq. 49.
Below minus h the sum is zero. On minus h to zero it is the prefix at x plus h.
Translation by h identifies its square mass with the prefix integral from zero to h.
The coefficient at index zero is zero, so the endpoint convention changes no mass. -/
theorem negative_mass_eq_I1 (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 1 ≤ h) (hhN : h ≤ N) :
    (∫ x : ℝ in Set.Iic 0, ‖movingSum (coefficients N) x h‖ ^ 2) = I1 N h := by
  have hs : Set.Icc (-h) 0 ⊆ Set.Iic (0 : ℝ) := fun _ hx => hx.2
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    (f := fun x : ℝ => ‖movingSum (coefficients N) x h‖ ^ 2) measurableSet_Iic hs (by
      intro x hx
      have hx0 : x ≤ 0 := hx.1
      have hxu : x + h ≤ 0 := by
        have hxnot := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hxnot
        rcases hxnot with hxlo | hxhi <;> linarith
      change ‖movingSum (coefficients N) x h‖ ^ 2 = 0
      rw [movingSum_eq_prefix_nonpos N hx0, weightedPrefix_nonpos N hxu]
      simp)
  calc (∫ x : ℝ in Set.Iic 0, ‖movingSum (coefficients N) x h‖ ^ 2)
      = ∫ x : ℝ in Set.Icc (-h) 0, ‖movingSum (coefficients N) x h‖ ^ 2 := he
    _ = ∫ x : ℝ in Set.Icc (-h) 0, weightedPrefix N (x + h) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change ‖movingSum (coefficients N) x h‖ ^ 2 = weightedPrefix N (x + h) ^ 2
      rw [movingSum_eq_prefix_nonpos N hx.2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ∫ x in (-h)..(0 : ℝ), weightedPrefix N (x + h) ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith : -h ≤ 0)]
    _ = I1 N h := by
      have hc := intervalIntegral.integral_comp_add_right
        (f := fun t : ℝ => weightedPrefix N t ^ 2) (a := -h) (b := 0) h
      simpa only [neg_add_cancel, zero_add, I1] using hc

/-- The exact moving_mass_split target follows from its two half line identities.
Spatial integrability is supplied by the proved indicator majorant argument. -/
theorem moving_mass_split_assembled (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 1 ≤ h) (hhN : h ≤ N) :
    (∫ x : ℝ, ‖movingSum (coefficients N) x h‖ ^ 2) = I1 N h + I2 N h := by
  have hi := Decomp402a.moving_square_integrable (coefficients N)
    (coefficients_summable N hN) h (by linarith)
  have hs := integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hi
  rw [Set.compl_Iic, negative_mass_eq_I1 N hN h hh hhN, positive_mass_eq_I2 N (by linarith)] at hs
  exact hs.symm

example : type_of% moving_mass_split = type_of% moving_mass_split_assembled := rfl

end LeanLab.GoldbachAverage.Decomp402d
