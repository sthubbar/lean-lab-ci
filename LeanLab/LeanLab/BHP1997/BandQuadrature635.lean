/-
P0069 page 51 display 5.17. An auxiliary rational band lower bound.
The number thirteen over ten is a lab certificate bound, not a printed paper constant.
The integer inner grid uses 160 by 160 cells and has lower sum 208352 over 160000.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem three_band_quadrature635 {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    13/10 ≤ ∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      if ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b))) then 1/(a*b^2) else 0 := by
  let R : ℝ → ℝ → Prop := fun a b => ((2273/10000 ≤ b ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧ a + 2*b ≤ 1) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 4*a + 3*b ≤ 15/8 ∧ 17/8 ≤ 4*a + 7*b ∧
            (a + b ≤ 7/16 ∨ 17/8 ≤ 4*a + 5*b) ∧
            (2273/10000 ≤ a ∨ a + 1/8 ≤ 2*b)) ∨
        (1/8 ≤ b ∧ b ≤ 2273/10000 ∧ b ≤ a ∧ a ≤ 1/2 ∧ 9/16 ≤ a + 2*b ∧
            a + 2*b ≤ 1 ∧ 17/8 ≤ 4*a + 3*b ∧
            (4*a + b ≤ 15/8 ∨ 17/8 ≤ 4*a + b)))
  let F : ℝ → ℝ → ℝ := fun a b => if R a b then 1 / (a * b ^ 2) else 0
  let good : ℕ → ℕ → Bool := fun i j =>
    let a := 40 + i; let A := a + 1; let b := 40 + j; let B := b + 1
    decide (B ≤ a ∧ 2 * A ≤ 400 ∧ 9 * 400 ≤ 16 * (a + 2 * b) ∧ A + 2 * B ≤ 400 ∧
      (2273 * 400 ≤ 10000 * b ∨
       (400 ≤ 8 * b ∧ 10000 * B ≤ 2273 * 400 ∧ 8 * (4 * A + 3 * B) ≤ 15 * 400 ∧
        17 * 400 ≤ 8 * (4 * a + 7 * b) ∧
        (16 * (A + B) ≤ 7 * 400 ∨ 17 * 400 ≤ 8 * (4 * a + 5 * b)) ∧
        (2273 * 400 ≤ 10000 * a ∨ 8 * A + 400 ≤ 16 * b)) ∨
       (400 ≤ 8 * b ∧ 10000 * B ≤ 2273 * 400 ∧ 17 * 400 ≤ 8 * (4 * a + 3 * b) ∧
        (8 * (4 * A + B) ≤ 15 * 400 ∨ 17 * 400 ≤ 8 * (4 * a + b)))))
  let w : ℕ → ℕ → ℕ := fun i j =>
    if good i j then 400 ^ 3 / ((41 + i) * (41 + j) ^ 2) else 0
  let p : ℕ → ℝ := fun n => (40 + (n : ℝ)) / 400
  have hp0 : p 0 = 1 / 10 := by norm_num [p]
  have hp160 : p 160 = 1 / 2 := by norm_num [p]
  have hpstep (n : ℕ) : p (n + 1) - p n = 1 / 400 := by simp [p]; ring
  have hpm : Monotone p := by
    intro i j hij
    dsimp [p]
    gcongr
  have hRM : MeasurableSet {z : ℝ × ℝ | R z.1 z.2} := by
    dsimp only [R]
    have hle : ∀ f g : ℝ × ℝ → ℝ, Continuous f → Continuous g →
        MeasurableSet {p | f p ≤ g p} := fun f g hf hg => (isClosed_le hf hg).measurableSet
    simp only [Set.ofPred_and, Set.ofPred_or]
    repeat' first
      | apply MeasurableSet.inter
      | apply MeasurableSet.union
      | (apply hle <;> fun_prop)
  have hFm : Measurable (fun z : ℝ × ℝ => F z.1 z.2) := by
    exact Measurable.ite hRM (by fun_prop) measurable_const
  have hFM (a b : ℝ) : |F a b| ≤ 1000 := by
    dsimp only [F, R]
    split_ifs with h
    · have hb1 : (1/8:ℝ) ≤ b := by
        rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · linarith
        · exact h1
        · exact h1
      have hba : b ≤ a := by
        rcases h with ⟨-, h2, -⟩ | ⟨-, -, h2, -⟩ | ⟨-, -, h2, -⟩
        · exact h2
        · exact h2
        · exact h2
      have hb2 : (1/64:ℝ) ≤ b^2 := by nlinarith
      have hmul : (1/8:ℝ)*(1/64) ≤ a*b^2 :=
        mul_le_mul (le_trans hb1 hba) hb2 (by norm_num) (by linarith)
      have hpos : 0 < a*b^2 := by linarith
      have hnn : 0 ≤ (1:ℝ)/(a*b^2) := by positivity
      rw [abs_of_nonneg hnn]
      rw [div_le_iff₀ hpos]
      linarith
    · norm_num
  have hFi (a lo hi : ℝ) : IntervalIntegrable (F a) volume lo hi := by
    have hm : Measurable (F a) := hFm.comp measurable_prodMk_left
    have hb (s : Set ℝ) : ∀ᵐ b ∂(volume.restrict s), ‖F a b‖ ≤ 1000 :=
      Filter.Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hFM a b
    exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _),
      Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _)⟩
  have hJi (j : ℕ) (lo hi : ℝ) :
      IntervalIntegrable (fun a => ∫ b in p j..p (j + 1), F a b) volume lo hi := by
    have h1 := (StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (p j) (p (j + 1)))) hFm.stronglyMeasurable).measurable
    have h2 := (StronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (p (j + 1)) (p j))) hFm.stronglyMeasurable).measurable
    have hm : Measurable (fun a => ∫ b in p j..p (j + 1), F a b) := h1.sub h2
    have hb (s : Set ℝ) : ∀ᵐ a ∂(volume.restrict s),
        ‖∫ b in p j..p (j + 1), F a b‖ ≤ 1000 * |p (j + 1) - p j| :=
      Filter.Eventually.of_forall fun a =>
        intervalIntegral.norm_integral_le_of_norm_le_const fun b hb => by
          rw [Real.norm_eq_abs]; exact hFM a b
    exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _),
      Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _)⟩
  have hpoint (i j : ℕ) (a b : ℝ) (ha : a ∈ Set.Icc (p i) (p (i + 1)))
      (hb : b ∈ Set.Icc (p j) (p (j + 1))) : (w i j : ℝ) ≤ F a b := by
    let ai : ℝ := 40 + (i : ℝ)
    let Ai : ℝ := 41 + (i : ℝ)
    let bj : ℝ := 40 + (j : ℝ)
    let Bj : ℝ := 41 + (j : ℝ)
    have hai : p (i + 1) = Ai / 400 := by dsimp [p, Ai]; push_cast; ring
    have hbj : p (j + 1) = Bj / 400 := by dsimp [p, Bj]; push_cast; ring
    change ai / 400 ≤ a ∧ a ≤ p (i + 1) at ha
    change bj / 400 ≤ b ∧ b ≤ p (j + 1) at hb
    rw [hai] at ha
    rw [hbj] at hb
    have ha0 : 0 < a := by dsimp [ai] at ha; linarith [Nat.cast_nonneg (α := ℝ) i]
    have hb0 : 0 < b := by dsimp [bj] at hb; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hAi : 0 < Ai := by dsimp [Ai]; positivity
    have hBj : 0 < Bj := by dsimp [Bj]; positivity
    dsimp only [w]
    split_ifs with hg
    · have hnat := of_decide_eq_true hg
      have hr : Bj ≤ ai ∧ 2 * Ai ≤ 400 ∧ 9 * 400 ≤ 16 * (ai + 2 * bj) ∧ Ai + 2 * Bj ≤ 400 ∧
          (2273 * 400 ≤ 10000 * bj ∨
           (400 ≤ 8 * bj ∧ 10000 * Bj ≤ 2273 * 400 ∧ 8 * (4 * Ai + 3 * Bj) ≤ 15 * 400 ∧
            17 * 400 ≤ 8 * (4 * ai + 7 * bj) ∧
            (16 * (Ai + Bj) ≤ 7 * 400 ∨ 17 * 400 ≤ 8 * (4 * ai + 5 * bj)) ∧
            (2273 * 400 ≤ 10000 * ai ∨ 8 * Ai + 400 ≤ 16 * bj)) ∨
           (400 ≤ 8 * bj ∧ 10000 * Bj ≤ 2273 * 400 ∧ 17 * 400 ≤ 8 * (4 * ai + 3 * bj) ∧
            (8 * (4 * Ai + Bj) ≤ 15 * 400 ∨ 17 * 400 ≤ 8 * (4 * ai + bj)))) := by
        dsimp [ai, Ai, bj, Bj]
        norm_cast <;> omega
      rcases hr with ⟨hba, hA, hlo, hhi, hband⟩
      have hba' : b ≤ a := by linarith
      have hA' : a ≤ 1 / 2 := by linarith
      have hlo' : 9 / 16 ≤ a + 2 * b := by linarith
      have hhi' : a + 2 * b ≤ 1 := by linarith
      have hreg : R a b := by
        dsimp only [R]
        rcases hband with hh | hm | hn
        · exact Or.inl ⟨by linarith, hba', hA', hlo', hhi'⟩
        · rcases hm with ⟨h1, h2, h3, h4, h5, h6⟩
          refine Or.inr (Or.inl ⟨by linarith, by linarith, hba', hA', hlo', hhi',
            by linarith, by linarith, ?_, ?_⟩)
          · rcases h5 with h5 | h5
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)
          · rcases h6 with h6 | h6
            · exact Or.inl (by linarith)
            · exact Or.inr (by linarith)
        · rcases hn with ⟨h1, h2, h3, h4⟩
          refine Or.inr (Or.inr ⟨by linarith, by linarith, hba', hA', hlo', hhi',
            by linarith, ?_⟩)
          rcases h4 with h4 | h4
          · exact Or.inl (by linarith)
          · exact Or.inr (by linarith)
      change ((400 ^ 3 / ((41 + i) * (41 + j) ^ 2) : ℕ) : ℝ) ≤ F a b
      rw [show F a b = 1 / (a * b ^ 2) by exact if_pos hreg]
      have hc : ((400 ^ 3 / ((41 + i) * (41 + j) ^ 2) : ℕ) : ℝ) ≤
          (400 : ℝ) ^ 3 / (Ai * Bj ^ 2) := by
        have h := (Nat.cast_div_le (α := ℝ) (m := 400 ^ 3) (n := (41 + i) * (41 + j) ^ 2))
        push_cast at h
        convert h using 1 <;> norm_num [Ai, Bj]
      apply hc.trans
      have heq : (400 : ℝ) ^ 3 / (Ai * Bj ^ 2) = 1 / ((Ai / 400) * (Bj / 400) ^ 2) := by
        field_simp <;> ring
      rw [heq]
      apply one_div_le_one_div_of_le (by positivity : 0 < a * b ^ 2)
      exact mul_le_mul ha.2 (pow_le_pow_left₀ hb0.le hb.2 2) (sq_nonneg _)
        (by positivity)
    · norm_num only [Nat.cast_zero]
      change (0 : ℝ) ≤ F a b
      dsimp only [F]
      split_ifs <;> positivity
  have hcell (i j : ℕ) : (w i j : ℝ) / 160000 ≤
      ∫ a in p i..p (i + 1), ∫ b in p j..p (j + 1), F a b := by
    have hi : p i ≤ p (i + 1) := hpm (Nat.le_succ _)
    have hj : p j ≤ p (j + 1) := hpm (Nat.le_succ _)
    have hinner (a : ℝ) (ha : a ∈ Set.Icc (p i) (p (i + 1))) :
        (1 / 400 : ℝ) * (w i j : ℝ) ≤ ∫ b in p j..p (j + 1), F a b := by
      have h := intervalIntegral.integral_mono_on hj
        (intervalIntegrable_const (c := (w i j : ℝ))) (hFi a _ _)
        (fun b hb => hpoint i j a b ha hb)
      simpa only [intervalIntegral.integral_const, smul_eq_mul, hpstep] using h
    have h := intervalIntegral.integral_mono_on hi
      (intervalIntegrable_const (c := ((1 / 400 : ℝ) * (w i j : ℝ)))) (hJi j _ _)
      hinner
    simp only [intervalIntegral.integral_const, smul_eq_mul, hpstep] at h
    convert h using 1 <;> ring
  have hfull : (∫ a in (1 / 10 : ℝ)..(1 / 2 : ℝ), ∫ b in (1 / 10 : ℝ)..(1 / 2 : ℝ), F a b) =
      ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160,
        ∫ a in p i..p (i + 1), ∫ b in p j..p (j + 1), F a b := by
    have hinner (a : ℝ) : (∫ b in (1 / 10 : ℝ)..(1 / 2 : ℝ), F a b) =
        ∑ j ∈ Finset.range 160, ∫ b in p j..p (j + 1), F a b := by
      have h := intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := 160)
        (fun j hj => hFi a (p j) (p (j + 1)))
      simpa only [hp0, hp160] using h.symm
    simp_rw [hinner]
    rw [intervalIntegral.integral_finsetSum (fun j hj => hJi j _ _)]
    have houter (j : ℕ) : (∫ a in (1 / 10 : ℝ)..(1 / 2 : ℝ), ∫ b in p j..p (j + 1), F a b) =
        ∑ i ∈ Finset.range 160, ∫ a in p i..p (i + 1), ∫ b in p j..p (j + 1), F a b := by
      have h := intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := 160)
        (fun i hi => hJi j (p i) (p (i + 1)))
      simpa only [hp0, hp160] using h.symm
    simp_rw [houter]
    exact Finset.sum_comm
  have hcert : (∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160, w i j) = 208352 := by
    dsimp only [w, good]
    set_option maxHeartbeats 0 in
      set_option maxRecDepth 100000 in
        decide +kernel
  have hcertR : (13 / 10 : ℝ) ≤
      ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160, (w i j : ℝ) / 160000 := by
    have hc : (208000 : ℝ) ≤ ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160, (w i j : ℝ) := by
      have hc : 208000 ≤ ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160, w i j := by omega
      exact_mod_cast hc
    simp_rw [← Finset.sum_div]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 160000)).2
    norm_num
    exact hc
  change (13 / 10 : ℝ) ≤ ∫ a in (1 / 10 : ℝ)..(1 / 2 : ℝ),
    ∫ b in (1 / 10 : ℝ)..(1 / 2 : ℝ), F a b
  apply hcertR.trans
  rw [hfull]
  exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hcell i j

end LeanLab.BHP1997.LowerShortC165
