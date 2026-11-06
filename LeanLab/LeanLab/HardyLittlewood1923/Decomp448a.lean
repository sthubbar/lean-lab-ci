import LeanLab.HardyLittlewood1923.Decomp415a
import LeanLab.HardyLittlewood1923.Decomp296Farey
import LeanLab.HardyLittlewood1923.Geometry448
import LeanLab.HardyLittlewood1923.Cover448
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 5 and 6 section 1.4 and page 22 equation 3.116.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp448a
open Real Finset MeasureTheory
open LeanLab.HardyLittlewood1923.Decomp276a

/-- P0004 pages 5 and 6 section 1.4. Reduced centers indexed by denominator and numerator. -/
def arcIndices (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Icc 1 N).sigma fun q => (range q).filter fun p => p.Coprime q

/-- P0004 pages 5 and 6 section 1.4. The actual translated half open Farey cell. -/
noncomputable def arcCell (N : ℕ) (i : Σ _ : ℕ, ℕ) : Set ℝ :=
  Set.Ioc (2 * π * (i.2 : ℝ) / i.1 + arcLeft N i.2 i.1)
    (2 * π * (i.2 : ℝ) / i.1 + arcRight N i.2 i.1)

/-- P0004 pages 5 and 6 section 1.4. Translate each local endpoint back to its mediant boundary. -/
theorem arcCell_eq (N : ℕ) (i : Σ _ : ℕ, ℕ) :
    arcCell N i = Set.Ioc
      (2 * π * (mediant (fareyPrev N ((i.2 : ℚ) / i.1)) ((i.2 : ℚ) / i.1) : ℝ))
      (2 * π * (mediant ((i.2 : ℚ) / i.1) (fareyNext N ((i.2 : ℚ) / i.1)) : ℝ)) := by
  unfold arcCell arcLeft arcRight
  simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast]
  congr 1 <;> ring

set_option maxHeartbeats 1000000 in
/-- LEAF. P0004 page 6 first sentence and the joined extreme intervals on page 5.
The translated cells cover the period starting at the left endpoint of the zero arc.
This finite geometric statement has no function, integral or prime coefficient. -/
theorem arcCell_cover {N : ℕ} (hN : 1 ≤ N) :
    (⋃ i ∈ arcIndices N, arcCell N i) =
      Set.Ioc (arcLeft N 0 1) (arcLeft N 0 1 + 2 * π) := by
  classical
  have hT : (0 : ℝ) < 2 * π := by positivity
  have hL : arcLeft N 0 1 = 2 * π * (mediant (fareyPrev N 0) 0 : ℝ) := by simp [arcLeft]
  ext θ
  constructor
  · intro hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hqi, hpi⟩ := mem_sigma.mp hi
    obtain ⟨hq, hqN⟩ := mem_Icc.mp hqi
    obtain ⟨hp, hpq⟩ := mem_filter.mp hpi
    have hpr := mem_range.mp hp
    let r : ℚ := (i.2 : ℚ) / i.1
    have hr : r ∈ fareyPoints N := Geometry448.center_mem hq hqN hpr hpq
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    have hr1 : r < 1 := (div_lt_one (by positivity : (0 : ℚ) < i.1)).mpr (by exact_mod_cast hpr)
    rw [arcCell_eq] at hx
    have hrat : θ / (2 * π) ∈
        (⋃ r ∈ (fareyPoints N).filter (fun r => 0 ≤ r ∧ r < 1),
          Set.Ioc (mediant (fareyPrev N r) r : ℝ) (mediant r (fareyNext N r) : ℝ)) := by
      refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hr, hr0, hr1⟩, ?_⟩⟩
      constructor
      · apply (lt_div_iff₀ hT).mpr
        dsimp [r]
        nlinarith only [hx.1]
      · apply (div_le_iff₀ hT).mpr
        dsimp [r]
        nlinarith only [hx.2]
    rw [Cover448.rational_cover hN] at hrat
    simp only [hL]
    have h1 := (lt_div_iff₀ hT).mp hrat.1
    have h2 := (div_le_iff₀ hT).mp hrat.2
    constructor <;> nlinarith only [h1, h2]
  · intro hx
    simp only [hL] at hx
    have hrat : θ / (2 * π) ∈
        Set.Ioc (mediant (fareyPrev N 0) 0 : ℝ) ((mediant (fareyPrev N 0) 0 : ℝ) + 1) := by
      constructor
      · apply (lt_div_iff₀ hT).mpr
        nlinarith only [hx.1]
      · apply (div_le_iff₀ hT).mpr
        nlinarith only [hx.2]
    rw [← Cover448.rational_cover hN] at hrat
    obtain ⟨r, hrat⟩ := Set.mem_iUnion.mp hrat
    obtain ⟨hr, hrat⟩ := Set.mem_iUnion.mp hrat
    obtain ⟨hrF, hr0, hr1⟩ := mem_filter.mp hr
    obtain ⟨p, q, hq, hqN, hp, hpq, hpval⟩ := Cover448.point_representation hrF hr0 hr1
    refine Set.mem_iUnion.mpr ⟨(⟨q, p⟩ : Σ _ : ℕ, ℕ), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hq, hqN⟩, mem_filter.mpr ⟨mem_range.mpr hp, hpq⟩⟩
    · rw [arcCell_eq, hpval]
      have h1 := (lt_div_iff₀ hT).mp hrat.1
      have h2 := (div_le_iff₀ hT).mp hrat.2
      constructor <;> nlinarith only [h1, h2]

/-- LEAF. P0004 pages 5 and 6 section 1.4. Distinct reduced centers have disjoint half open cells. -/
theorem arcCell_disjoint {N : ℕ} (hN : 1 ≤ N) :
    Set.Pairwise (arcIndices N : Set (Σ _ : ℕ, ℕ)) (fun i j => Disjoint (arcCell N i) (arcCell N j)) := by
  intro i hi j hj hij
  obtain ⟨hi1, hi2⟩ := mem_sigma.mp hi
  obtain ⟨hj1, hj2⟩ := mem_sigma.mp hj
  obtain ⟨hqi, hqiN⟩ := mem_Icc.mp hi1
  obtain ⟨hqj, hqjN⟩ := mem_Icc.mp hj1
  obtain ⟨hpi, hcpi⟩ := mem_filter.mp hi2
  obtain ⟨hpj, hcpj⟩ := mem_filter.mp hj2
  have hpiq := mem_range.mp hpi
  have hpjq := mem_range.mp hpj
  let r : ℚ := (i.2 : ℚ) / i.1
  let s : ℚ := (j.2 : ℚ) / j.1
  have hr : r ∈ fareyPoints N := Geometry448.center_mem hqi hqiN hpiq hcpi
  have hs : s ∈ fareyPoints N := Geometry448.center_mem hqj hqjN hpjq hcpj
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hr1 : r ≤ 1 := (div_le_one (by positivity : (0 : ℚ) < i.1)).mpr (by exact_mod_cast hpiq.le)
  have hs1 : s ≤ 1 := (div_le_one (by positivity : (0 : ℚ) < j.1)).mpr (by exact_mod_cast hpjq.le)
  have hne : r ≠ s := by
    intro he
    obtain ⟨hnum, hden⟩ := Geometry448.center_injective hqi hqj hcpi hcpj he
    exact hij (Sigma.ext hden (heq_of_eq hnum))
  rw [arcCell_eq, arcCell_eq]
  apply Set.disjoint_left.mpr
  intro θ hθi hθj
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · have hm := Geometry448.mediant_order hN hr hs hr0 hs1 hrs
    have hmR : (mediant r (fareyNext N r) : ℝ) ≤ mediant (fareyPrev N s) s := by exact_mod_cast hm
    have ht := mul_le_mul_of_nonneg_left hmR (by positivity : 0 ≤ 2 * π)
    dsimp [r, s] at ht
    linarith [hθi.2, hθj.1]
  · have hm := Geometry448.mediant_order hN hs hr hs0 hr1 hsr
    have hmR : (mediant s (fareyNext N s) : ℝ) ≤ mediant (fareyPrev N r) r := by exact_mod_cast hm
    have ht := mul_le_mul_of_nonneg_left hmR (by positivity : 0 ≤ 2 * π)
    dsimp [r, s] at ht
    linarith [hθj.2, hθi.1]

/-- P0004 page 6, positive arc widths make each cell an ordinary oriented interval. -/
theorem arcCell_order {N : ℕ} (hN : 1 ≤ N) {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ arcIndices N) :
    2 * π * (i.2 : ℝ) / i.1 + arcLeft N i.2 i.1 ≤
      2 * π * (i.2 : ℝ) / i.1 + arcRight N i.2 i.1 := by
  obtain ⟨hq, hp⟩ := mem_sigma.mp hi
  obtain ⟨hq1, hqN⟩ := mem_Icc.mp hq
  obtain ⟨hpq, hcop⟩ := mem_filter.mp hp
  have hw := Decomp296Farey.arc_widths hN hq1 hqN (mem_range.mp hpq) hcop
  have hpos : 0 < 1 / (2 * (i.1 : ℝ) * N) := by positivity
  linarith [hw.1, hw.2]

/-- P0004 page 22 equation 3.116. Translation identifies each local integral with its cell. -/
theorem integral_arcCell {N : ℕ} (hN : 1 ≤ N) {i : Σ _ : ℕ, ℕ}
    (hi : i ∈ arcIndices N) (f : ℝ → ℂ) :
    (∫ θ in arcLeft N i.2 i.1..arcRight N i.2 i.1,
      f (2 * π * (i.2 : ℝ) / i.1 + θ)) = ∫ θ in arcCell N i, f θ := by
  rw [intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_of_le (arcCell_order hN hi)]
  rfl

set_option maxHeartbeats 1000000 in
/-- P0004 page 22 equation 3.116.
The exact sealed geometric target follows from finite covering and separation.
Finite covering and disjointness are proved. -/
theorem farey_integral_dissection {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℂ)
    (hf : Continuous f) (hp : Function.Periodic f (2 * π)) :
    (∑ q ∈ Icc 1 N, ∑ p ∈ (range q).filter (fun p => p.Coprime q),
      ∫ θ in arcLeft N p q..arcRight N p q, f (2 * π * (p : ℝ) / q + θ)) =
        ∫ θ in (0 : ℝ)..(2 * π), f θ := by
  have hc := integral_biUnion_finset (μ := volume) (f := f) (s := arcCell N) (arcIndices N)
    (fun i _ => (measurableSet_Ioc : MeasurableSet (arcCell N i)))
    (arcCell_disjoint hN)
    (fun i _ => hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  have hrewrite :
      (∑ q ∈ Icc 1 N, ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcLeft N p q..arcRight N p q, f (2 * π * (p : ℝ) / q + θ)) =
      ∑ q ∈ Icc 1 N, ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcCell N ⟨q, p⟩, f θ := by
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro p hpq
    exact integral_arcCell (i := ⟨q, p⟩) hN (mem_sigma.mpr ⟨hq, hpq⟩) f
  have hsum := Finset.sum_sigma (Icc 1 N)
    (fun q => (range q).filter (fun p => p.Coprime q))
    (fun i : Σ _ : ℕ, ℕ => ∫ θ in arcCell N i, f θ)
  calc
    _ = ∑ i ∈ arcIndices N, ∫ θ in arcCell N i, f θ := hrewrite.trans hsum.symm
    _ = ∫ θ in ⋃ i ∈ arcIndices N, arcCell N i, f θ := hc.symm
    _ = ∫ θ in Set.Ioc (arcLeft N 0 1) (arcLeft N 0 1 + 2 * π), f θ := by
      rw [arcCell_cover hN]
    _ = ∫ θ in arcLeft N 0 1..arcLeft N 0 1 + 2 * π, f θ :=
      (intervalIntegral.integral_of_le (by linarith [Real.pi_pos] :
        arcLeft N 0 1 ≤ arcLeft N 0 1 + 2 * π)).symm
    _ = ∫ θ in (0 : ℝ)..(2 * π), f θ := by
      simpa only [zero_add] using hp.intervalIntegral_add_eq (arcLeft N 0 1) 0

#print axioms arcCell_eq
#print axioms arcCell_order
#print axioms integral_arcCell
#print axioms arcCell_cover
#print axioms arcCell_disjoint
#print axioms farey_integral_dissection
end LeanLab.HardyLittlewood1923.Decomp448a
