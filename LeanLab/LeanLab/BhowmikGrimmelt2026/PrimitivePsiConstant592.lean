/-
The high zero estimate in Davenport second edition chapter 19 page 118.
The full strip zero window count gives an absolute logarithmic budget for paired reciprocals.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.PrimitivePsiEstimates592

namespace LeanLab.BhowmikGrimmelt2026

/-- Numerical logarithm budget for the unit windows in Davenport page 118. -/
theorem modulus_log_sqrt_budget592 {q j : ℕ} [NeZero q] (hj : 1 ≤ j) :
    Real.log ((q : ℝ) * ((j : ℝ) + 3)) ≤
      9 * Real.log (2 * (q : ℝ)) * Real.sqrt j := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hq0 : (0 : ℝ) < q := by linarith
  have hroot1 : 1 ≤ Real.sqrt (j : ℝ) := Real.one_le_sqrt.mpr hj1
  have hroot0 : 0 ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  have hL : 1 / 2 ≤ Real.log (2 * (q : ℝ)) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 * (q : ℝ) by linarith)
    linarith [Real.log_two_gt_d9]
  have hlogq : Real.log q ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log hq0 (by linarith)
  have hsqrt : Real.sqrt ((j : ℝ) + 3) ≤ 2 * Real.sqrt (j : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ j by positivity)]
  have hlogj : Real.log ((j : ℝ) + 3) ≤ 4 * Real.sqrt (j : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr
      (show (0 : ℝ) < (j : ℝ) + 3 by positivity))
    rw [Real.log_sqrt (by positivity)] at hh
    linarith
  have h1 : Real.log (2 * (q : ℝ)) ≤
      Real.log (2 * (q : ℝ)) * Real.sqrt (j : ℝ) :=
    le_mul_of_one_le_right (by linarith) hroot1
  have h2 := mul_le_mul_of_nonneg_right hL hroot0
  rw [Real.log_mul hq0.ne' (by positivity)]
  nlinarith

/-- Davenport page 118, the paired high zero correction has a uniform logarithmic
absolute mass. The proof uses the full strip unit window count and a convergent
three halves power series. It requires neither GRH nor ZeroBound. -/
theorem high_zero_paired_mass592 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (Z : Finset ℂ),
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 1 ≤ |ρ.im|) →
      ∑ ρ ∈ Z, (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖ ≤
        C * Real.log (2 * (q : ℝ)) := by
  classical
  obtain ⟨A, hA, hcount⟩ := zero_window_count508
  have hsum : Summable (fun j : ℕ => 1 / (j : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  let S : ℝ := ∑' j : ℕ, 1 / (j : ℝ) ^ (3 / 2 : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun j => by positivity)
  refine ⟨72 * A * S, by positivity, ?_⟩
  intro q _ χ Z hzeros
  let bucket : ℂ → ℕ := fun ρ => ⌊|ρ.im|⌋₊
  let J := Z.image bucket
  let L : ℝ := Real.log (2 * (q : ℝ))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hjpos (j : ℕ) (hj : j ∈ J) : 1 ≤ j := by
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hj
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (hzeros ρ hρ).2.2.2
  have hfiber (j : ℕ) (hj : j ∈ J) :
      ∑ ρ ∈ Z with bucket ρ = j, (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖ ≤
        72 * A * L / (j : ℝ) ^ (3 / 2 : ℝ) := by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hjpos j hj
    have hj0 : (0 : ℝ) < j := by linarith
    let F := Z.filter (fun ρ => bucket ρ = j)
    have hrange (ρ : ℂ) (hρ : ρ ∈ F) :
        (j : ℝ) ≤ |ρ.im| ∧ |ρ.im| < (j : ℝ) + 1 := by
      obtain ⟨_, hb⟩ := Finset.mem_filter.mp hρ
      change ⌊|ρ.im|⌋₊ = j at hb
      have hlow := Nat.floor_le (abs_nonneg ρ.im)
      have hhigh := Nat.lt_floor_add_one |ρ.im|
      rw [hb] at hlow hhigh
      exact ⟨hlow, hhigh⟩
    have hp := hcount q χ ((j : ℝ) + 1 / 2) (F.filter (fun ρ => 0 ≤ ρ.im)) (by
      intro ρ hρ
      obtain ⟨hf, hsign⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, h0, h1, _⟩ := hzeros ρ (Finset.mem_filter.mp hf).1
      have hr := hrange ρ hf
      rw [abs_of_nonneg hsign] at hr
      refine ⟨hz, h0, h1, ?_⟩
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2])
    have hm := hcount q χ (-((j : ℝ) + 1 / 2)) (F.filter (fun ρ => ¬ 0 ≤ ρ.im)) (by
      intro ρ hρ
      obtain ⟨hf, hsign⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, h0, h1, _⟩ := hzeros ρ (Finset.mem_filter.mp hf).1
      have hr := hrange ρ hf
      rw [abs_of_neg (lt_of_not_ge hsign)] at hr
      refine ⟨hz, h0, h1, ?_⟩
      rw [abs_le]
      constructor <;> linarith [hr.1, hr.2])
    rw [abs_of_pos (by linarith : 0 < (j : ℝ) + 1 / 2)] at hp
    rw [abs_neg, abs_of_pos (by linarith : 0 < (j : ℝ) + 1 / 2)] at hm
    have hlog : Real.log ((q : ℝ) * ((j : ℝ) + 1 / 2 + 2)) ≤
        9 * L * Real.sqrt j := by
      apply le_trans _ (modulus_log_sqrt_budget592 (q := q) (hjpos j hj))
      apply Real.log_le_log (by positivity)
      nlinarith
    have hsplit := Finset.sum_filter_add_sum_filter_not F (fun ρ : ℂ => 0 ≤ ρ.im)
      (fun ρ => (mult χ ρ : ℝ))
    have hmass : ∑ ρ ∈ F, (mult χ ρ : ℝ) ≤ 18 * A * L * Real.sqrt j := by
      have hp' := hp.trans (mul_le_mul_of_nonneg_left hlog hA)
      have hm' := hm.trans (mul_le_mul_of_nonneg_left hlog hA)
      linarith
    have hterm (ρ : ℂ) (hρ : ρ ∈ F) :
        (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖ ≤
          (mult χ ρ : ℝ) * (4 / (j : ℝ) ^ 2) := by
      have hz := hzeros ρ (Finset.mem_filter.mp hρ).1
      have hp := paired_zero_reciprocal_bound541 hz.2.2.2
      have hr := (hrange ρ hρ).1
      have hden : (j : ℝ) ^ 2 ≤ 1 + ρ.im ^ 2 := by
        have hh := (sq_le_sq₀ hj0.le (abs_nonneg ρ.im)).mpr hr
        rw [sq_abs] at hh
        linarith
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact hp.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden)
    have hpow : (j : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (j : ℝ) = (j : ℝ) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hj0]
      norm_num [Real.rpow_natCast]
    have hquot : Real.sqrt (j : ℝ) / (j : ℝ) ^ 2 = 1 / (j : ℝ) ^ (3 / 2 : ℝ) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).mpr
      simpa [mul_comm] using hpow
    calc ∑ ρ ∈ F, (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖
        ≤ ∑ ρ ∈ F, (mult χ ρ : ℝ) * (4 / (j : ℝ) ^ 2) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ F, (mult χ ρ : ℝ)) * (4 / (j : ℝ) ^ 2) := by rw [Finset.sum_mul]
      _ ≤ (18 * A * L * Real.sqrt j) * (4 / (j : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = 72 * A * L * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) := by ring
      _ = 72 * A * L / (j : ℝ) ^ (3 / 2 : ℝ) := by rw [hquot]; ring
  have hmaps : ∀ ρ ∈ Z, bucket ρ ∈ J := fun ρ hρ => Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
  calc ∑ ρ ∈ Z, (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖
      = ∑ j ∈ J, ∑ ρ ∈ Z with bucket ρ = j,
          (mult χ ρ : ℝ) * ‖1 / ρ + 1 / (2 - ρ)‖ :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ j ∈ J, 72 * A * L / (j : ℝ) ^ (3 / 2 : ℝ) := Finset.sum_le_sum hfiber
    _ = 72 * A * L * ∑ j ∈ J, 1 / (j : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 72 * A * L * S := mul_le_mul_of_nonneg_left
      (hsum.sum_le_tsum J (fun _ _ => by positivity)) (by positivity)
    _ = (72 * A * S) * L := by ring

end LeanLab.BhowmikGrimmelt2026
