/-
P0088 page 7 before display 27. Finite kernel mass estimates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.KernelBase687
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace LeanLab.KumchevLiu2007.Task687
open Real MeasureTheory LeanLab.KumchevLiu2007 KernelSumSplit1122
open scoped BigOperators Topology

/-- P0088 page 7 before display 27: the finite symmetric Fourier kernel. -/
noncomputable def kernelDirichlet (N : ℕ) (t : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range (N + 1), Real.cos (2 * π * (i : ℝ) * t) - 1

/-- P0088 page 7 before display 27: the symmetric kernel mass outside an arc. -/
noncomputable def kernelMass (b : ℝ) (N : ℕ) : ℝ :=
  2 * ∫ t in b..(1 / 2 : ℝ), kernelDirichlet N t

/-- Finite Dirichlet identity, auxiliary for P0088 page 7 before display 27. -/
theorem kernelDirichlet_mul_sin (N : ℕ) (t : ℝ) :
    Real.sin (π * t) * kernelDirichlet N t = Real.sin ((2 * (N : ℝ) + 1) * π * t) := by
  have h := Real.sin_mul_sum_cos (N + 1) (2 * π * t) 0
  have he1 : 2 * π * t / 2 = π * t := by ring
  have he2 : (((N + 1 : ℕ) : ℝ) * (2 * π * t) / 2) = ((N : ℝ) + 1) * π * t := by push_cast; ring
  have he3 : ((((N + 1 : ℕ) : ℝ) - 1) * (2 * π * t) / 2 + 0) = (N : ℝ) * π * t := by push_cast; ring
  have hs : (∑ i ∈ Finset.range (N + 1), Real.cos ((2 * π * t) * i + 0)) =
      ∑ i ∈ Finset.range (N + 1), Real.cos (2 * π * (i : ℝ) * t) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ring
  rw [he1, he2, he3, hs] at h
  have hp : 2 * Real.sin (((N : ℝ) + 1) * π * t) * Real.cos ((N : ℝ) * π * t) =
      Real.sin ((2 * (N : ℝ) + 1) * π * t) + Real.sin (π * t) := by
    rw [Real.two_mul_sin_mul_cos]
    rw [add_comm (Real.sin _) (Real.sin _)]
    congr 1 <;> congr 1 <;> ring
  unfold kernelDirichlet
  nlinarith [hp]

/-- The finite kernel is continuous. -/
theorem kernelDirichlet_continuous (N : ℕ) : Continuous (kernelDirichlet N) := by
  unfold kernelDirichlet
  fun_prop

/-- The finite kernel is bounded by three times its positive index count. -/
theorem kernelDirichlet_abs_le (N : ℕ) (t : ℝ) :
    |kernelDirichlet N t| ≤ 3 * ((N : ℝ) + 1) := by
  let S := ∑ i ∈ Finset.range (N + 1), Real.cos (2 * π * (i : ℝ) * t)
  have hs : |S| ≤ (N : ℝ) + 1 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N + 1), |Real.cos (2 * π * (i : ℝ) * t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun i hi => Real.abs_cos_le_one _)
      _ = (N : ℝ) + 1 := by simp
  have hh : |2 * S - 1| ≤ 2 * |S| + 1 := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_two, abs_one] using (norm_sub_le (2 * S) (1 : ℝ))
  change |2 * S - 1| ≤ _
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The zeroth symmetric mass is the constant Fourier coefficient. -/
theorem kernelMass_zero (b : ℝ) : kernelMass b 0 = 1 - 2 * b := by
  simp [kernelMass, kernelDirichlet, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Oscillatory sine integrals have the elementary reciprocal frequency bound. -/
theorem sine_integral_bound (c a d : ℝ) (hc : 0 < c) :
    |∫ t in a..d, Real.sin (c * t)| ≤ 2 / c := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.sin) c (a := a) (b := d)
  rw [integral_sin] at h
  have he : |c * ∫ t in a..d, Real.sin (c * t)| ≤ 2 := by
    rw [h, abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos (c*a), Real.cos_le_one (c*a),
      Real.neg_one_le_cos (c*d), Real.cos_le_one (c*d)]
  rw [abs_mul, abs_of_pos hc] at he
  apply (le_div_iff₀ hc).2
  nlinarith

/-- The symmetric finite kernel mass decays past the arc endpoint. -/
theorem kernelMass_decay (b : ℝ) (N : ℕ) (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    |kernelMass b N| ≤ 2 / (b * ((N : ℝ) + 1)) := by
  let c : ℝ := (2 * (N : ℝ) + 1) * π
  have hc : 0 < c := by dsimp [c]; positivity
  have hs (t : ℝ) (ht : t ∈ Set.Icc b (1/2 : ℝ)) : 2*b ≤ Real.sin (π*t) := by
    have hh := Real.mul_le_sin (x := π*t) (by apply mul_nonneg Real.pi_pos.le; linarith [ht.1])
      (by nlinarith [ht.2, Real.pi_pos])
    have he : 2/π * (π*t) = 2*t := by field_simp
    rw [he] at hh
    linarith [ht.1]
  have hf : AntitoneOn (fun t : ℝ => 1 / Real.sin (π*t)) (Set.Icc b (1/2 : ℝ)) := by
    intro x hx y hy hxy
    apply one_div_le_one_div_of_le (by nlinarith [hs x hx])
    apply Real.monotoneOn_sin
    · constructor <;> nlinarith [hx.1, hx.2, Real.pi_pos]
    · constructor <;> nlinarith [hy.1, hy.2, Real.pi_pos]
    · exact mul_le_mul_of_nonneg_left hxy Real.pi_pos.le
  have hg : IntervalIntegrable (fun t : ℝ => Real.sin (c*t)) volume b (1/2 : ℝ) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.sin (c*t))).intervalIntegrable _ _
  obtain ⟨ξ, hξ, hξb⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn hb'
      (by norm_num [show π*(1/2 : ℝ) = π/2 by ring, Real.sin_pi_div_two] : 0 ≤ 1 / Real.sin (π*(1/2 : ℝ))) hf hg
  have hid : (∫ t in b..(1/2 : ℝ), (1 / Real.sin (π*t)) • Real.sin (c*t)) =
      ∫ t in b..(1/2 : ℝ), kernelDirichlet N t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc b (1/2 : ℝ) := by simpa only [Set.uIcc_of_le hb'] using ht
    have hst : Real.sin (π*t) ≠ 0 := ne_of_gt (by nlinarith [hs t ht'])
    change (1 / Real.sin (π*t)) * Real.sin (c*t) = _
    have hi := kernelDirichlet_mul_sin N t
    dsimp [c]
    rw [← hi]
    field_simp
  rw [hid, Real.norm_eq_abs, Real.norm_eq_abs] at hξb
  have hsb : 2*b ≤ Real.sin (π*b) := hs b ⟨le_rfl, hb'⟩
  have hrec : 1 / Real.sin (π*b) ≤ 1 / (2*b) :=
    one_div_le_one_div_of_le (by positivity) hsb
  have hi : |∫ t in b..(1/2 : ℝ), kernelDirichlet N t| ≤ 1/(2*b) * (2/c) := by
    exact hξb.trans (mul_le_mul hrec (sine_integral_bound c b ξ hc)
      (abs_nonneg _) (by positivity))
  unfold kernelMass
  rw [abs_mul, abs_two]
  have hpi : 1 ≤ π := le_trans (by norm_num : (1:ℝ) ≤ 3) Real.pi_gt_three.le
  have hn : (N : ℝ) + 1 ≤ c := by dsimp [c]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hrec' := one_div_le_one_div_of_le (by positivity : 0 < (N : ℝ)+1) hn
  have he : 2 * (1 / (2*b) * (2/c)) = 2/b * (1/c) := by field_simp
  calc
    _ ≤ 2 * (1/(2*b) * (2/c)) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = 2/b * (1/c) := he
    _ ≤ 2/b * (1/((N:ℝ)+1)) := mul_le_mul_of_nonneg_left hrec' (by positivity)
    _ = _ := by field_simp

/-- The symmetric finite kernel mass has a uniform absolute bound. -/
theorem kernelMass_bounded (b : ℝ) (N : ℕ) (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    |kernelMass b N| ≤ 8 := by
  by_cases hN : N = 0
  · subst N
    rw [kernelMass_zero, abs_le]
    constructor <;> linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN)
  let δ : ℝ := 1 / ((N : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1/2 := by dsimp [δ]; apply (div_le_iff₀ (by positivity)).2; linarith
  by_cases hbd : δ ≤ b
  · have hh := kernelMass_decay b N hb hb'
    have hbn : 1 ≤ b * ((N : ℝ) + 1) := by
      have hd : δ * ((N : ℝ) + 1) = 1 := by dsimp [δ]; field_simp
      nlinarith [mul_le_mul_of_nonneg_right hbd (by positivity : 0 ≤ (N : ℝ)+1)]
    have hh' : 2 / (b * ((N : ℝ) + 1)) ≤ 2 := by
      apply (div_le_iff₀ (by positivity)).2; linarith
    linarith
  · have hbd' : b ≤ δ := le_of_not_ge hbd
    have hint (x y : ℝ) : IntervalIntegrable (kernelDirichlet N) volume x y :=
      (kernelDirichlet_continuous N).intervalIntegrable _ _
    have he : kernelMass b N = 2 * (∫ t in b..δ, kernelDirichlet N t) + kernelMass δ N := by
      unfold kernelMass
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint b δ) (hint δ (1/2))]
      ring
    have hi : |∫ t in b..δ, kernelDirichlet N t| ≤ 3 * ((N : ℝ)+1) * (δ-b) := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := b) (b := δ) (fun t _ => (show ‖kernelDirichlet N t‖ ≤ 3*((N:ℝ)+1) by
          simpa only [Real.norm_eq_abs] using kernelDirichlet_abs_le N t))
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hbd')] using hh
    have hm : |kernelMass δ N| ≤ 2 := by
      have hh := kernelMass_decay δ N hδ hδ'
      have hd : δ * ((N : ℝ) + 1) = 1 := by dsimp [δ]; field_simp
      simpa only [hd, div_one] using hh
    have hd : ((N : ℝ)+1) * δ = 1 := by dsimp [δ]; field_simp
    rw [he]
    calc
      _ ≤ |2 * (∫ t in b..δ, kernelDirichlet N t)| + |kernelMass δ N| := abs_add_le _ _
      _ ≤ 2 * (3*((N:ℝ)+1)*(δ-b)) + 2 := by
        rw [abs_mul, abs_two]
        nlinarith
      _ ≤ 8 := by nlinarith [mul_nonneg (by positivity : 0 ≤ (N:ℝ)+1) hb.le]

/-- The symmetric finite kernel mass has both uniform size and endpoint decay. -/
theorem kernelMass_min_bound (b : ℝ) (N : ℕ) (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    |kernelMass b N| ≤ 8 * min 1 (1 / (b * ((N : ℝ) + 1))) := by
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 8)]
  apply le_min
  · simpa using kernelMass_bounded b N hb hb'
  · have hh := kernelMass_decay b N hb hb'
    have hp : 0 ≤ 1 / (b * ((N : ℝ)+1)) := by positivity
    have he : 2 / (b * ((N:ℝ)+1)) = 2 * (1 / (b * ((N:ℝ)+1))) := by ring
    rw [he] at hh
    linarith

/-- Adding a frequency adds its two equal Fourier coefficients to the mass. -/
theorem kernelMass_succ (b : ℝ) (N : ℕ) :
    kernelMass b (N+1) = kernelMass b N + 2 * Kb b (N+1 : ℕ) := by
  have hd (t : ℝ) : kernelDirichlet (N+1) t = kernelDirichlet N t +
      2 * Real.cos (2*π*((N+1:ℕ):ℝ)*t) := by
    unfold kernelDirichlet
    rw [Finset.sum_range_succ]
    ring
  have hc : (2*π*((N+1:ℕ):ℝ)) ≠ 0 := by positivity
  have hcos := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos)
    (2*π*((N+1:ℕ):ℝ)) (a := b) (b := (1/2:ℝ))
  rw [integral_cos] at hcos
  have he : 2*π*((N+1:ℕ):ℝ)*(1/2:ℝ) = ((N+1:ℕ):ℝ)*π := by ring
  rw [he, Real.sin_nat_mul_pi] at hcos
  have hik : IntervalIntegrable (kernelDirichlet N) volume b (1/2:ℝ) :=
    (kernelDirichlet_continuous N).intervalIntegrable _ _
  have hic : IntervalIntegrable (fun t : ℝ => 2 * Real.cos (2*π*((N+1:ℕ):ℝ)*t)) volume b (1/2:ℝ) :=
    (by fun_prop : Continuous (fun t : ℝ => 2 * Real.cos (2*π*((N+1:ℕ):ℝ)*t))).intervalIntegrable _ _
  have hkb : Kb b (N+1 : ℕ) = -Real.sin (2*π*((N+1:ℕ):ℝ)*b) / (π*((N+1:ℕ):ℝ)) := by
    simp [Kb, Nat.cast_add, Nat.cast_one, show (N:ℤ)+1 ≠ 0 by omega, neg_div]
  unfold kernelMass
  simp_rw [hd]
  rw [intervalIntegral.integral_add hik hic, intervalIntegral.integral_const_mul, hkb]
  have hn : (π*((N+1:ℕ):ℝ)) ≠ 0 := by positivity
  field_simp
  nlinarith [hcos]

/-- The mass is exactly the finite symmetric coefficient sum. -/
theorem kernelMass_eq_sum (b : ℝ) (N : ℕ) :
    kernelMass b N = Kb b 0 + 2 * ∑ i ∈ Finset.range N, Kb b (i+1 : ℕ) := by
  induction N with
  | zero => simp [kernelMass_zero, Kb]
  | succ N ih => rw [kernelMass_succ, Finset.sum_range_succ, ih]; ring

/-- A symmetric finite sum of the paper's kernel has endpoint decay. -/
theorem kernel_symmetric_sum_bound (b : ℝ) (N : ℕ) (hb : 0 < b) (hb' : b ≤ 1/2) :
    |Kb b 0 + 2 * ∑ i ∈ Finset.range N, Kb b (i+1 : ℕ)| ≤
      8 * min 1 (1 / (b * ((N : ℝ) + 1))) := by
  rw [← kernelMass_eq_sum]
  exact kernelMass_min_bound b N hb hb'

end LeanLab.KumchevLiu2007.Task687

#print axioms LeanLab.KumchevLiu2007.Task687.kernelDirichlet_mul_sin
#print axioms LeanLab.KumchevLiu2007.Task687.kernelDirichlet_continuous
#print axioms LeanLab.KumchevLiu2007.Task687.kernelDirichlet_abs_le
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_zero
#print axioms LeanLab.KumchevLiu2007.Task687.sine_integral_bound
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_decay
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_bounded
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_min_bound
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_succ
#print axioms LeanLab.KumchevLiu2007.Task687.kernelMass_eq_sum
#print axioms LeanLab.KumchevLiu2007.Task687.kernel_symmetric_sum_bound
