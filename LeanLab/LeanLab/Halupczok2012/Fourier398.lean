import LeanLab.Halupczok2012.Circle398

/-!
Perelli Pintz pages 43 to 44, the finite Fourier identity behind display 1.
PNTPort already proves additive character orthogonality.
Mathlib supplies the measurable integral partition.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Fourier398

open Finset MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt
open Decomp398a LeanLab.PNTPort.LargeSieve

/-- The coefficient extraction used on page 44, on any unit interval.
This is PNTPort orthogonality and periodic integration. -/
theorem phase_integral (k : ℤ) (u : ℝ) :
    (∫ α in Set.Icc u (u + 1), phase ((k : ℝ) * α)) = if k = 0 then 1 else 0 := by
  change (∫ α in Set.Icc u (u + 1), e ((k : ℝ) * α)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : u ≤ u + 1)]
  have hper : Function.Periodic (fun α : ℝ => e ((k : ℝ) * α)) 1 := by
    intro α
    dsimp only
    rw [mul_add, mul_one, e_add, e_int, mul_one]
  rw [hper.intervalIntegral_add_eq u (-(1 / 2))]
  convert LeanLab.PNTPort.Gallagher.integral_e_int k using 1 <;> norm_num

/-- The major arcs on page 43 are measurable, since they form a countable union of open sets. -/
theorem major_measurable (N Y ε A : ℝ) : MeasurableSet (majorArcs N Y ε A) := by
  unfold majorArcs
  refine measurableSet_Icc.inter ?_
  have he : {α : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ (3 / ε * (2 * A + 25)) ∧
      1 ≤ a ∧ a ≤ q ∧ a.Coprime q ∧
      |α - (a : ℝ) / q| < Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / ((q : ℝ) * Y)} =
      ⋃ q : ℕ, ⋃ a : ℕ, if 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ (3 / ε * (2 * A + 25)) ∧
        1 ≤ a ∧ a ≤ q ∧ a.Coprime q then
        {α : ℝ | |α - (a : ℝ) / q| <
          Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / ((q : ℝ) * Y)} else ∅ := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, a, hq, hq', ha, haq, hcop, hα⟩
      refine ⟨q, a, ?_⟩
      rw [if_pos ⟨hq, hq', ha, haq, hcop⟩]
      exact hα
    · rintro ⟨q, a, h⟩
      split_ifs at h with hc
      · exact ⟨q, a, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, h⟩
      · exact False.elim h
  rw [he]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  split_ifs
  · exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  · exact MeasurableSet.empty

/-- Perelli Pintz page 44, finite Fourier extraction of the additive relation h + j = m. -/
theorem finite_convolution (U V : Finset ℕ) (w z : ℕ → ℂ) (m : ℕ) (u : ℝ) :
    (∫ α in Set.Icc u (u + 1),
      (∑ h ∈ U, w h * phase ((h : ℝ) * α)) *
      (∑ j ∈ V, z j * phase ((j : ℝ) * α)) * phase (-(m : ℝ) * α)) =
      ∑ h ∈ U, ∑ j ∈ V, if h + j = m then w h * z j else 0 := by
  have he : ∀ α : ℝ,
      (∑ h ∈ U, w h * phase ((h : ℝ) * α)) *
      (∑ j ∈ V, z j * phase ((j : ℝ) * α)) * phase (-(m : ℝ) * α) =
      ∑ h ∈ U, ∑ j ∈ V, (w h * z j) * phase ((((h : ℤ) + j - m : ℤ) : ℝ) * α) := by
    intro α
    rw [sum_mul_sum, sum_mul]
    refine sum_congr rfl fun h _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    dsimp [phase]
    have hp : (((h : ℤ) + j - m : ℤ) : ℝ) * α = (h : ℝ) * α + (j : ℝ) * α + -(m : ℝ) * α := by
      push_cast
      ring
    rw [hp, e_add, e_add]
    ring
  have hi : ∀ h j : ℕ, IntegrableOn
      (fun α : ℝ => (w h * z j) * phase ((((h : ℤ) + j - m : ℤ) : ℝ) * α)) (Set.Icc u (u + 1)) := by
    intro h j
    apply Continuous.integrableOn_Icc
    dsimp [phase]
    exact continuous_const.mul
      (LeanLab.PNTPort.Gallagher.continuous_e_mul _)
  simp_rw [he]
  rw [integral_finsetSum U (fun h _ => integrable_finsetSum V (fun j _ => hi h j))]
  refine sum_congr rfl fun h _ => ?_
  rw [integral_finsetSum V (fun j _ => hi h j)]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, phase_integral]
  have hc : (h : ℤ) + j - m = 0 ↔ h + j = m := by omega
  simp only [hc]
  split_ifs <;> simp

/-- The paper's real interval notation, page 43, expressed as membership in kRange. -/
theorem window_mem (X R : ℝ) (k : ℕ) :
    k ∈ kRange X R ↔ X < (k : ℝ) ∧ (k : ℝ) ≤ X + R := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, h⟩
    exact_mod_cast h.2.trans (Nat.le_ceil (X + R))

/-- The finite additive convolution is exactly R star, with the cutoffs on page 43. -/
theorem convolution_value (N Y : ℝ) (hYN : Y ≤ N) (m : ℕ) :
    (∑ h ∈ kRange (N - Y) Y, ∑ j ∈ kRange 0 Y,
      if h + j = m then (Λ h : ℂ) * (Λ j : ℂ) else 0) = (ppR m N Y : ℂ) := by
  have hval : ∀ h ∈ kRange (N - Y) Y,
      (∑ j ∈ kRange 0 Y, if h + j = m then (Λ h : ℂ) * (Λ j : ℂ) else 0) =
      if h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y then (Λ h : ℂ) * (Λ (m - h) : ℂ) else 0 := by
    intro h hh
    have hh' := (window_mem _ _ _).mp hh
    by_cases hp : h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y
    · rw [if_pos hp]
      have hj : m - h ∈ kRange 0 Y := by
        rw [window_mem]
        refine ⟨by exact_mod_cast (show 0 < m - h by omega), by simpa using hp.2⟩
      rw [sum_eq_single (m - h)]
      · rw [if_pos (by omega)]
      · intro j hj hne
        rw [if_neg (by omega)]
      · exact fun hn => False.elim (hn hj)
    · rw [if_neg hp]
      apply sum_eq_zero
      intro j hj
      rw [if_neg]
      intro he
      have hj' := (window_mem _ _ _).mp hj
      have hjpos : 0 < j := by exact_mod_cast hj'.1
      have hjm : j = m - h := by omega
      exact hp ⟨by omega, by simpa [hjm] using hj'.2⟩
  have hset : (kRange (N - Y) Y).filter (fun h => h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y) =
      (Ioo 0 m).filter (ppCond m N Y) := by
    ext h
    simp only [mem_filter, window_mem, mem_Ioo, ppCond]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hm, hY⟩
      have hp : (0 : ℝ) < h := by linarith
      exact ⟨⟨by exact_mod_cast hp, hm⟩, hlo, by linarith, hY⟩
    · rintro ⟨⟨h0, hm⟩, hlo, hhi, hY⟩
      exact ⟨⟨hlo, by linarith⟩, hm, hY⟩
  calc
    _ = ∑ h ∈ kRange (N - Y) Y,
        if h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y then (Λ h : ℂ) * (Λ (m - h) : ℂ) else 0 :=
      sum_congr rfl hval
    _ = ∑ h ∈ (kRange (N - Y) Y).filter (fun h => h < m ∧ ((m - h : ℕ) : ℝ) ≤ Y),
        (Λ h : ℂ) * (Λ (m - h) : ℂ) := (sum_filter _ _).symm
    _ = _ := by rw [hset, ppR]; push_cast; rfl

/-- Perelli Pintz page 44 display 1 before the arc split.
The full unit interval coefficient equals R star exactly. -/
theorem full_coefficient (N Y ε : ℝ) (hYN : Y ≤ N) (m : ℕ) :
    arcCoeff N Y m (arcBase Y ε) = (ppR m N Y : ℂ) := by
  unfold arcCoeff arcBase firstPoly secondPoly
  simpa only [add_comm] using (finite_convolution (kRange (N - Y) Y) (kRange 0 Y)
    (fun h => (Λ h : ℂ)) (fun j => (Λ j : ℂ)) m
    (1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2))).trans (convolution_value N Y hYN m)

/-- The exact major and minor arc partition behind display 1 on page 44. -/
theorem partition (ε A N Y : ℝ) (hYN : Y ≤ N) (m : ℕ) :
    (ppR m N Y : ℂ) = arcCoeff N Y m (majorArcs N Y ε A) +
      arcCoeff N Y m (arcBase Y ε \ majorArcs N Y ε A) := by
  have hc : Continuous (fun α : ℝ => firstPoly N Y α * secondPoly Y α * phase (-(m : ℝ) * α)) := by
    unfold firstPoly secondPoly phase LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hi : IntegrableOn (fun α : ℝ => firstPoly N Y α * secondPoly Y α * phase (-(m : ℝ) * α))
      (arcBase Y ε) := hc.integrableOn_Icc
  have hd := setIntegral_sdiff (major_measurable N Y ε A) hi
    (show majorArcs N Y ε A ⊆ arcBase Y ε from Set.inter_subset_left)
  change arcCoeff N Y m (arcBase Y ε \ majorArcs N Y ε A) =
    arcCoeff N Y m (arcBase Y ε) - arcCoeff N Y m (majorArcs N Y ε A) at hd
  rw [hd, full_coefficient N Y ε hYN m]
  ring

end LeanLab.Halupczok2012.Fourier398
