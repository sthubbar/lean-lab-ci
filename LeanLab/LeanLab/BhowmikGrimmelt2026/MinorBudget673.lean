/-
The available minor arc estimate gives logarithm power nine.
Source: P0029 page 27, the minor arc step of display 7.8.
This bound leaves the sealed logarithm power five targets open.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp525a
import LeanLab.BhowmikGrimmelt2026.PrimeMinorReduction451
import LeanLab.BhowmikGrimmelt2026.MinorUniform451

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

/-- A bounded cutoff without the paper support can leave a prime in the supposed defect. -/
theorem bounded_cutoff_defect_counterexample673 :
    Sphi (fun _ => 1) 1 0 -
      (∑ n ∈ (Finset.range (2 + 1)).filter (fun n => n.Prime),
        ((vonMangoldt n * (1 : ℝ) : ℝ) : ℂ) * ee (0 * n)) = -(Real.log 2 : ℂ) ∧
      nonprimeSphi451 (fun _ => 1) 1 0 = 0 := by
  norm_num [Sphi, nonprimeSphi451, Finset.sum_filter, Finset.sum_range_succ,
    vonMangoldt_apply_prime Nat.prime_two, ee]

/-- Support of the paper cutoff makes the prime sum independent of the longer truncation. -/
theorem primeSphi_extend673 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {N X : ℕ} (hNX : N ≤ X)
    (α : ℝ) :
    (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
      ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) = primeSphi451 ϕ N α := by
  classical
  have hext :
      (∑ n ∈ Finset.range (N + 1),
        ((if n.Prime then vonMangoldt n * ϕ (n / N) else 0 : ℝ) : ℂ) * ee (α * n)) =
      ∑ n ∈ Finset.range (X + 1),
        ((if n.Prime then vonMangoldt n * ϕ (n / N) else 0 : ℝ) : ℂ) * ee (α * n) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro n _ hn
    have hnN : N < n := by simp only [Finset.mem_range] at hn; omega
    by_cases hN : N = 0
    · subst N
      have hz : ϕ 0 = 0 := by
        by_contra h
        have hs := hϕ.supp (subset_tsupport ϕ h)
        linarith [hs.1]
      simp [hz]
    · have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
      have hnle : (N : ℝ) ≤ n := by exact_mod_cast hnN.le
      rw [phi_zero_ge_one261 hϕ ((le_div_iff₀ hNp).mpr (by simpa using hnle))]
      simp
  calc
    _ = ∑ n ∈ Finset.range (X + 1),
        ((if n.Prime then vonMangoldt n * ϕ (n / N) else 0 : ℝ) : ℂ) * ee (α * n) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hp : n.Prime <;> simp [hp]
    _ = _ := hext.symm

open scoped Classical in
/-- The higher prime power defect has the printed budget for an admissible paper cutoff. -/
theorem nonprime_defect_phi673 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x, |ϕ x| ≤ M) {X : ℕ} (hX : 2 ≤ X) (ϑ : ℝ) :
    (∑ N ∈ Finset.Icc 1 X,
      ‖∫ α in (0 : ℝ)..1,
        if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (Sphi ϕ N α ^ 2 -
            (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
              ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2) *
            ee (-(N * α))‖ ^ 2) ≤
      192 * M ^ 4 * (X : ℝ) ^ (13 / 5 : ℝ) * Real.log X ^ 5 := by
  classical
  let W : ℕ → ℝ → ℂ := fun N α =>
    if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else ee (-(N * α))
  have hW (N : ℕ) (α : ℝ) : ‖W N α‖ ≤ 1 := by
    by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α
    · simp [W, hm]
    · simp only [W, if_neg hm, ee_eq_library84, LeanLab.PNTPort.LargeSieve.norm_e,
        le_refl]
  have hb := prime_power_family_log5_451 hM hbound hX W hW
  convert hb using 1
  apply Finset.sum_congr rfl
  intro N hN
  congr 2
  apply intervalIntegral.integral_congr
  intro α _
  dsimp only
  rw [primeSphi_extend673 hϕ (Finset.mem_Icc.mp hN).2 α]
  by_cases hm : MajorArc X ((X : ℝ) ^ ϑ) α <;> simp [W, hm]

open scoped Classical in
/-- The support sensitive family estimate and the available pointwise bound give power nine. -/
theorem minor_bare_log9_673 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ R : ℝ, 1 ≤ R → R ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, if MajorArc X R α then 0 else
          Sphi ϕ N α ^ 2 * ee (-(N * α))‖ ^ 2 ≤
        C * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) * X * Real.log X ^ 9 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hϕ.compact hϕ.smooth (by simp)
  refine ⟨192 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4, by positivity, ?_⟩
  intro X hX R hR hRX
  let W : ℝ → ℂ := {α | ¬ MajorArc X R α}.indicator (fun _ => 1)
  let U : ℝ := (L : ℝ) *
    (48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4)
  have hW : Measurable W := measurable_const.indicator (measurableSet_majorArc84 X R).compl
  have hWB (α : ℝ) : ‖W α‖ ≤ 1 := by
    classical
    by_cases hm : MajorArc X R α <;> simp [W, Set.indicator, hm]
  have hsup (n : ℕ) (hn : n ≤ X) (α : ℝ) (hne : W α ≠ 0) : ‖Sphi ϕ n α‖ ≤ U := by
    have hm : ¬ MajorArc X R α := by
      intro hm
      exact hne (by simp [W, Set.indicator, hm])
    exact Sphi_minor261 hϕ hL hX hR hRX hn hm
  have hfam := supported_family_sharp261 hϕ hL hX hW (by norm_num : (0 : ℝ) ≤ 1)
    (by dsimp [U]; positivity) hWB hsup
  have heq (N : ℕ) :
      (∫ α in (0 : ℝ)..1, if MajorArc X R α then 0 else
        Sphi ϕ N α ^ 2 * ee (-(N * α))) =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    apply intervalIntegral.integral_congr
    intro α _
    classical
    by_cases hm : MajorArc X R α <;> simp [W, Set.indicator, hm]
  simp_rw [heq]
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := by linarith
  have ha : ((X : ℝ) / Real.sqrt R) ^ 2 = (X : ℝ) ^ 2 / R := by
    rw [div_pow, Real.sq_sqrt hRp.le]
  have hb : ((X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 = (X : ℝ) ^ (8 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  have hs : ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 ≤
      2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ)) := by
    rw [← ha, ← hb]
    nlinarith only [sq_nonneg ((X : ℝ) / Real.sqrt R - (X : ℝ) ^ (4 / 5 : ℝ))]
  calc
    _ ≤ 96 * (1 : ℝ) ^ 2 * U ^ 2 * (L : ℝ) ^ 2 * X * Real.log X := hfam
    _ = 96 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4 *
        ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) ^ 2 * X * Real.log X ^ 9 := by
      dsimp [U]
      ring
    _ ≤ 96 * (48600 : ℝ) ^ 2 * (L : ℝ) ^ 4 *
        (2 * ((X : ℝ) ^ 2 / R + (X : ℝ) ^ (8 / 5 : ℝ))) * X * Real.log X ^ 9 := by
      gcongr
    _ = _ := by ring

open scoped Classical in
/-- Every subfamily of the prime restricted minor coefficients has the proved power nine budget. -/
theorem prime_minor_subfamily_log9_673 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ s : Finset ℕ, s ⊆ Finset.Icc 1 X →
      ∑ N ∈ s,
        ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
          (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
            ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 9 := by
  classical
  obtain ⟨B, hB, hb⟩ := minor_bare_log9_328 hϕ ϑ hϑ hϑ'
  obtain ⟨D, hD, hd⟩ := minor_prime_defect_family451 hϕ ϑ
  refine ⟨2 * B + 32 * D, by positivity, ?_⟩
  intro X hX s hs
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hbare := hb X hX
  have hdefect := hd X hX
  have hbudget := minor_budget_identity451 hXp ((X : ℝ) ^ ϑ)
  have hbare' : (∑ N ∈ Finset.Icc 1 X, ‖minorBare328 ϕ X N ϑ‖ ^ 2) ≤
      B * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 9 := by
    calc
      _ ≤ B * ((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) *
          X * Real.log X ^ 9 := hbare
      _ = B * (((X : ℝ) ^ 2 / (X : ℝ) ^ ϑ + (X : ℝ) ^ (8 / 5 : ℝ)) * X) *
          Real.log X ^ 9 := by ring
      _ = _ := by rw [hbudget]; ring
  have hlogs : Real.log (X : ℝ) ^ 5 ≤ 16 * Real.log X ^ 9 := by
    calc
      _ = Real.log (X : ℝ) * Real.log X ^ 4 := by ring
      _ ≤ (16 * Real.log (X : ℝ) ^ 5) * Real.log X ^ 4 :=
        mul_le_mul_of_nonneg_right (log_le_sixteen_log5_525 hX) (by positivity)
      _ = _ := by ring
  have hdefect' : (∑ N ∈ Finset.Icc 1 X,
      ‖minorBare328 ϕ X N ϑ - minorPrime451 ϕ X N ϑ‖ ^ 2) ≤
      16 * D * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 9 := by
    apply hdefect.trans
    calc
      _ ≤ D * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * (16 * Real.log X ^ 9) := by
        exact mul_le_mul_of_nonneg_left hlogs (by positivity)
      _ = _ := by ring
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => minorPrime451 ϕ X N ϑ) (fun N => minorBare328 ϕ X N ϑ)
  have hrev : (∑ N ∈ Finset.Icc 1 X,
      ‖minorPrime451 ϕ X N ϑ - minorBare328 ϕ X N ϑ‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X,
        ‖minorBare328 ϕ X N ϑ - minorPrime451 ϕ X N ϑ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N _
    rw [norm_sub_rev]
  rw [hrev] at hsplit
  have hfull : (∑ N ∈ Finset.Icc 1 X, ‖minorPrime451 ϕ X N ϑ‖ ^ 2) ≤
      (2 * B + 32 * D) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 9 := by
    nlinarith only [hsplit, hbare', hdefect']
  have heq (N : ℕ) (hN : N ∈ s) :
      (∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else
        (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime),
          ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))) =
      minorPrime451 ϕ X N ϑ := by
    unfold minorPrime451
    apply intervalIntegral.integral_congr
    intro α _
    dsimp only
    rw [primeSphi_extend673 hϕ (Finset.mem_Icc.mp (hs hN)).2 α]
  calc
    _ = ∑ N ∈ s, ‖minorPrime451 ϕ X N ϑ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [heq N hN]
    _ ≤ ∑ N ∈ Finset.Icc 1 X, ‖minorPrime451 ϕ X N ϑ‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (by intro N _ _; positivity)
    _ ≤ _ := hfull

/-- Four surplus logarithms cannot be absorbed into a constant on the natural number range. -/
theorem log9_not_absorbed673 (C : ℝ) :
    ∃ X : ℕ, 2 ≤ X ∧ C * Real.log X ^ 5 < Real.log X ^ 9 := by
  let t : ℝ := max C 2 + 1
  let X : ℕ := ⌈Real.exp t⌉₊
  have ht : 3 ≤ t := by dsimp [t]; linarith [le_max_right C 2]
  have hCt : C < t := by dsimp [t]; linarith [le_max_left C 2]
  have hceil : Real.exp t ≤ (X : ℝ) := Nat.le_ceil _
  have hX2 : (2 : ℝ) ≤ X := by linarith [Real.add_one_le_exp t]
  have hXp : (0 : ℝ) < X := by linarith
  have hlog : t ≤ Real.log X := (Real.le_log_iff_exp_le hXp).mpr hceil
  have hlog1 : 1 ≤ Real.log X := by linarith
  have hpow : Real.log X ≤ Real.log X ^ 4 := le_self_pow₀ hlog1 (by norm_num)
  have hCpow : C < Real.log X ^ 4 := by linarith
  refine ⟨X, by exact_mod_cast hX2, ?_⟩
  calc
    C * Real.log X ^ 5 < Real.log X ^ 4 * Real.log X ^ 5 :=
      mul_lt_mul_of_pos_right hCpow (by positivity)
    _ = Real.log X ^ 9 := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.primeSphi_extend673
#print axioms LeanLab.BhowmikGrimmelt2026.bounded_cutoff_defect_counterexample673
#print axioms LeanLab.BhowmikGrimmelt2026.nonprime_defect_phi673
#print axioms LeanLab.BhowmikGrimmelt2026.minor_bare_log9_673
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_subfamily_log9_673
#print axioms LeanLab.BhowmikGrimmelt2026.log9_not_absorbed673
