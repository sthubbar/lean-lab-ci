import LeanLab.RieselVaughan1983.Lemma2LogMoments

/-! Differentiation of G near zero for the page 51 moment displays.
AI wrote the Lean code. Binary Goldbach is OPEN.
The evaluated Euler-product derivatives remain separate proof obligations. -/
namespace LeanLab.RieselVaughan1983.Lemma2
open Real Set
noncomputable section

def gTerm (n : ℕ) (w : ℝ) : ℝ := g n * (n : ℝ) ^ (-w)
def gTermFirst (n : ℕ) (w : ℝ) : ℝ := -g n * Real.log n * (n : ℝ) ^ (-w)
def gTermSecond (n : ℕ) (w : ℝ) : ℝ := g n * Real.log n ^ 2 * (n : ℝ) ^ (-w)
def GFirst (w : ℝ) : ℝ := ∑' n : ℕ, gTermFirst n w

lemma log_le_sixth_root (n : ℕ) (hn : 0 < n) :
    Real.log n ≤ 6 * (n : ℝ) ^ (1 / 6 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.add_one_le_exp (Real.log n / 6)
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.exp (Real.log n / 6) = Real.exp (Real.log n * (1 / 6 : ℝ)) := by congr 1; ring
  rw [he] at h
  linarith

lemma log_sq_le_sixth_root (n : ℕ) (hn : 0 < n) :
    Real.log n ^ 2 ≤ 72 * (n : ℝ) ^ (1 / 6 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := Real.quadratic_le_exp_of_nonneg (x := Real.log n / 6) (by positivity)
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.exp (Real.log n / 6) = Real.exp (Real.log n * (1 / 6 : ℝ)) := by congr 1; ring
  rw [he] at h
  nlinarith

lemma sixth_root_sq (n : ℕ) :
    (n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · rw [← Real.rpow_add (by exact_mod_cast hn : (0 : ℝ) < n)]
    norm_num

lemma gTerm_hasDerivAt (n : ℕ) (w : ℝ) : HasDerivAt (gTerm n) (gTermFirst n w) w := by
  change HasDerivAt (fun x => g n * (n : ℝ) ^ (-x)) (gTermFirst n w) w
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [gTermFirst] using hasDerivAt_const w (0 : ℝ)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (HasDerivAt.const_rpow hn0 (hasDerivAt_id w).neg).const_mul (g n)
    convert h using 1 <;> dsimp [gTermFirst] <;> ring

lemma gTermFirst_hasDerivAt (n : ℕ) (w : ℝ) :
    HasDerivAt (gTermFirst n) (gTermSecond n w) w := by
  change HasDerivAt (fun x => -g n * Real.log n * (n : ℝ) ^ (-x)) (gTermSecond n w) w
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [gTermSecond] using hasDerivAt_const w (0 : ℝ)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h := (HasDerivAt.const_rpow hn0 (hasDerivAt_id w).neg).const_mul (-g n * Real.log n)
    convert h using 1 <;> dsimp [gTermSecond] <;> ring

lemma gTermFirst_bound (n : ℕ) (w : ℝ) (hw : -(1 / 6 : ℝ) < w) :
    ‖gTermFirst n w‖ ≤ 6 * mass n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gTermFirst, mass]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hr := Real.rpow_nonneg (Nat.cast_nonneg n) (-w)
    have hpow : (n : ℝ) ^ (-w) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [gTermFirst, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg hl, abs_of_nonneg hr]
    calc _ ≤ |g n| * (6 * (n : ℝ) ^ (1 / 6 : ℝ)) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          gcongr
          exact log_le_sixth_root n hn
      _ = 6 * mass n := by unfold mass; rw [show |g n| * (6 * (n : ℝ) ^ (1 / 6 : ℝ)) *
          (n : ℝ) ^ (1 / 6 : ℝ) = 6 * |g n| * ((n : ℝ) ^ (1 / 6 : ℝ) *
          (n : ℝ) ^ (1 / 6 : ℝ)) by ring, sixth_root_sq]; ring

lemma gTermSecond_bound (n : ℕ) (w : ℝ) (hw : -(1 / 6 : ℝ) < w) :
    ‖gTermSecond n w‖ ≤ 72 * mass n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gTermSecond, mass]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hr := Real.rpow_nonneg (Nat.cast_nonneg n) (-w)
    have hpow : (n : ℝ) ^ (-w) ≤ (n : ℝ) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [gTermSecond, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (Real.log n)), abs_of_nonneg hr]
    calc _ ≤ |g n| * (72 * (n : ℝ) ^ (1 / 6 : ℝ)) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          gcongr
          exact log_sq_le_sixth_root n hn
      _ = 72 * mass n := by unfold mass; rw [show |g n| * (72 * (n : ℝ) ^ (1 / 6 : ℝ)) *
          (n : ℝ) ^ (1 / 6 : ℝ) = 72 * |g n| * ((n : ℝ) ^ (1 / 6 : ℝ) *
          (n : ℝ) ^ (1 / 6 : ℝ)) by ring, sixth_root_sq]; ring

lemma G_hasDerivAt (w : ℝ) (hw : -(1 / 6 : ℝ) < w) : HasDerivAt G (GFirst w) w := by
  have h0 : Summable (fun n : ℕ => gTerm n 0) := by
    simpa [gTerm] using g_summable_norm.of_norm
  exact hasDerivAt_tsum_of_isPreconnected (mass_summable.mul_left 6)
    isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n y _ => gTerm_hasDerivAt n y)
    (fun n y hy => gTermFirst_bound n y hy) (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ))) h0 hw

lemma GFirst_hasDerivAt (w : ℝ) (hw : -(1 / 6 : ℝ) < w) :
    HasDerivAt GFirst (∑' n : ℕ, gTermSecond n w) w := by
  have h0 : Summable (fun n : ℕ => gTermFirst n 0) := by
    simpa [gTermFirst, neg_mul] using log_moment_summable_norm.of_norm.neg
  exact hasDerivAt_tsum_of_isPreconnected (mass_summable.mul_left 72)
    isOpen_Ioi (convex_Ioi _).isPreconnected
    (fun n y _ => gTermFirst_hasDerivAt n y)
    (fun n y hy => gTermSecond_bound n y hy) (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ))) h0 hw

lemma G_deriv_zero : deriv G 0 = -moment 1 := by
  rw [(G_hasDerivAt 0 (by norm_num)).deriv]
  simp [GFirst, gTermFirst, moment, tsum_neg, neg_mul]

lemma G_second_deriv_zero : deriv (deriv G) 0 = moment 2 := by
  have he : deriv G =ᶠ[nhds (0 : ℝ)] GFirst := by
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioi (-(1 / 6 : ℝ)))] with w hw
    exact (G_hasDerivAt w hw).deriv
  rw [Filter.EventuallyEq.deriv_eq he]
  rw [(GFirst_hasDerivAt 0 (by norm_num)).deriv]
  simp [gTermSecond, moment]

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.log_le_sixth_root
#print axioms LeanLab.RieselVaughan1983.Lemma2.log_sq_le_sixth_root
#print axioms LeanLab.RieselVaughan1983.Lemma2.sixth_root_sq
#print axioms LeanLab.RieselVaughan1983.Lemma2.gTerm_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.gTermFirst_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.gTermFirst_bound
#print axioms LeanLab.RieselVaughan1983.Lemma2.gTermSecond_bound
#print axioms LeanLab.RieselVaughan1983.Lemma2.G_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.GFirst_hasDerivAt
#print axioms LeanLab.RieselVaughan1983.Lemma2.G_deriv_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.G_second_deriv_zero
