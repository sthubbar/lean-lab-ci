import LeanLab.LanguascoPerelli1996.Interpolation318

/-!
Finite real weight partial summation for P0071 page 355 display 13.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Partial318
open Complex Real MeasureTheory Interpolation318

/-- Page 355 display 13, derived weighted Cauchy Schwarz for a finite combination. -/
theorem norm_sum_sq_le {κ : Type*} (t : Finset κ) (a : κ → ℝ) (z : κ → ℂ)
    (ha : ∀ k ∈ t, 0 ≤ a k) :
    ‖∑ k ∈ t, (a k : ℂ) * z k‖ ^ 2 ≤
      (∑ k ∈ t, a k) * ∑ k ∈ t, a k * ‖z k‖ ^ 2 := by
  have hn : ‖∑ k ∈ t, (a k : ℂ) * z k‖ ≤ ∑ k ∈ t, a k * ‖z k‖ := by
    calc
      _ ≤ ∑ k ∈ t, ‖(a k : ℂ) * z k‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha k hk)]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t ha
    (fun k hk => mul_nonneg (ha k hk) (sq_nonneg ‖z k‖))
    (fun k hk => le_of_eq (show (a k * ‖z k‖) ^ 2 = a k * (a k * ‖z k‖ ^ 2) by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

/-- Page 355 display 13, derived finite convex mass inequality. -/
theorem mass_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (c : κ → ι → ℂ) (γ : ι → ℝ) (a : κ → ℝ) (ha : ∀ k ∈ t, 0 ≤ a k) :
    mass s (fun i => ∑ k ∈ t, (a k : ℂ) * c k i) γ ≤
      (∑ k ∈ t, a k) * ∑ k ∈ t, a k * mass s (c k) γ := by
  classical
  have hp (v : ℝ) :
      ‖∑ i ∈ s, (∑ k ∈ t, (a k : ℂ) * c k i) * Complex.exp (Complex.I * γ i * v)‖ ^ 2 ≤
        (∑ k ∈ t, a k) * ∑ k ∈ t, a k *
          ‖∑ i ∈ s, c k i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 := by
    have he : (∑ i ∈ s, (∑ k ∈ t, (a k : ℂ) * c k i) * Complex.exp (Complex.I * γ i * v)) =
        ∑ k ∈ t, (a k : ℂ) * ∑ i ∈ s, c k i * Complex.exp (Complex.I * γ i * v) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    exact norm_sum_sq_le t a _ ha
  have hi (k : κ) := (FiniteEnergy108.finite_energy_identity s (c k) γ).1
  have hl := (FiniteEnergy108.finite_energy_identity s
    (fun i => ∑ k ∈ t, (a k : ℂ) * c k i) γ).1
  have hr : Integrable (fun v : ℝ =>
      (∑ k ∈ t, a k) * ∑ k ∈ t, a k *
        (‖∑ i ∈ s, c k i * Complex.exp (Complex.I * γ i * v)‖ ^ 2 *
          Real.exp (-2 * |v|))) :=
    (integrable_finsetSum t (fun k _ => (hi k).const_mul (a k))).const_mul _
  have hh := integral_mono hl hr (fun v => by
    convert mul_le_mul_of_nonneg_right (hp v) (Real.exp_pos (-2 * |v|)).le using 1 <;>
      simp only [Finset.sum_mul, mul_assoc])
  change mass s _ γ ≤ _ at hh
  rw [integral_const_mul, integral_finsetSum t (fun k _ => (hi k).const_mul (a k))] at hh
  simp_rw [integral_const_mul] at hh
  exact hh

/-- Page 355 display 13, derived mass equality for coefficients equal on the index set. -/
theorem mass_congr {ι : Type*} (s : Finset ι) (c d : ι → ℂ) (γ : ι → ℝ)
    (h : ∀ i ∈ s, c i = d i) : mass s c γ = mass s d γ := by
  unfold mass
  congr 1
  funext v
  have he : (∑ i ∈ s, c i * Complex.exp (Complex.I * γ i * v)) =
      ∑ i ∈ s, d i * Complex.exp (Complex.I * γ i * v) :=
    Finset.sum_congr rfl (fun i hi => by rw [h i hi])
  rw [he]

/-- Page 355 display 13, derived invariance of mass under a common minus sign. -/
theorem mass_neg {ι : Type*} (s : Finset ι) (c : ι → ℂ) (γ : ι → ℝ) :
    mass s (fun i => -c i) γ = mass s c γ := by
  unfold mass
  simp only [neg_mul, Finset.sum_neg_distrib, norm_neg]

/-- Page 355 display 13, derived finite Abel estimate for monotone real weights.
No positive frequency assumption is made. Only the multiplier is monotone. -/
theorem monotone_mass_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (f : ℕ → ι → ℂ) (w : ℕ → ℝ) (N : ℕ) {M : ℝ}
    (hM : 0 ≤ M) (hw0 : 0 ≤ w 0) (hw : Monotone w)
    (hmass : ∀ k, k ≤ N → mass s (fun i => ∑ j ∈ Finset.range (k + 1), f j i) γ ≤ M) :
    mass s (fun i => ∑ k ∈ Finset.range (N + 1), (w k : ℂ) * f k i) γ ≤
      4 * w N ^ 2 * M := by
  classical
  let a : ℕ → ℝ := fun k => if k = N then w N else w (k + 1) - w k
  let c : ℕ → ι → ℂ := fun k i =>
    if k = N then ∑ j ∈ Finset.range (N + 1), f j i
    else -(∑ j ∈ Finset.range (k + 1), f j i)
  have ha (k : ℕ) (_hk : k ∈ Finset.range (N + 1)) : 0 ≤ a k := by
    dsimp only [a]
    split_ifs
    · exact hw0.trans (hw (Nat.zero_le N))
    · exact sub_nonneg.mpr (hw (Nat.le_succ k))
  have hcoef (i : ι) : (∑ k ∈ Finset.range (N + 1), (a k : ℂ) * c k i) =
      ∑ k ∈ Finset.range (N + 1), (w k : ℂ) * f k i := by
    have hh := Finset.sum_range_by_parts (fun k => (w k : ℂ)) (fun k => f k i) (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at hh
    rw [Finset.sum_range_succ]
    have hs : (∑ k ∈ Finset.range N, (a k : ℂ) * c k i) =
        -(∑ k ∈ Finset.range N, ((w (k + 1) : ℂ) - (w k : ℂ)) *
          ∑ j ∈ Finset.range (k + 1), f j i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≠ N := Nat.ne_of_lt (Finset.mem_range.mp hk)
      simp only [a, c, if_neg hkN, Complex.ofReal_sub, mul_neg]
    rw [hs]
    simp only [a, c, if_pos rfl]
    linear_combination -hh
  have hc (k : ℕ) (_hk : k ∈ Finset.range (N + 1)) : mass s (c k) γ ≤ M := by
    dsimp only [c]
    split_ifs with hk
    · exact hmass N le_rfl
    · rw [mass_neg]
      exact hmass k (Nat.le_of_lt_succ (Finset.mem_range.mp _hk))
  have hsum : (∑ k ∈ Finset.range (N + 1), a k) = 2 * w N - w 0 := by
    rw [Finset.sum_range_succ]
    have hs : (∑ k ∈ Finset.range N, a k) = w N - w 0 := by
      calc
        _ = ∑ k ∈ Finset.range N, (w (k + 1) - w k) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [a, if_neg (Nat.ne_of_lt (Finset.mem_range.mp hk))]
        _ = _ := Finset.sum_range_sub w N
    rw [hs]
    simp only [a, if_pos rfl]
    ring
  have hs0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), a k := Finset.sum_nonneg ha
  have hsle : (∑ k ∈ Finset.range (N + 1), a k) ≤ 2 * w N := by rw [hsum]; linarith
  have hh := mass_sum_le s (Finset.range (N + 1)) c γ a ha
  simp only [hcoef] at hh
  have hb : (∑ k ∈ Finset.range (N + 1), a k * mass s (c k) γ) ≤
      (∑ k ∈ Finset.range (N + 1), a k) * M := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hc k hk) (ha k hk))
  calc
    _ ≤ (∑ k ∈ Finset.range (N + 1), a k) * ∑ k ∈ Finset.range (N + 1), a k * mass s (c k) γ := hh
    _ ≤ (∑ k ∈ Finset.range (N + 1), a k) ^ 2 * M := by
      nlinarith [mul_le_mul_of_nonneg_left hb hs0]
    _ ≤ 4 * w N ^ 2 * M := by
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs0 hsle 2) hM
      nlinarith

end LeanLab.LanguascoPerelli1996.Partial318

#print axioms LeanLab.LanguascoPerelli1996.Partial318.norm_sum_sq_le
#print axioms LeanLab.LanguascoPerelli1996.Partial318.mass_sum_le

#print axioms LeanLab.LanguascoPerelli1996.Partial318.mass_neg
#print axioms LeanLab.LanguascoPerelli1996.Partial318.monotone_mass_le

#print axioms LeanLab.LanguascoPerelli1996.Partial318.mass_congr
