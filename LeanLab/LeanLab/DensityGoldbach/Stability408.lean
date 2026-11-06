/-
Explicit Fourier stability for Shao 1206.6139v2 page 14, Lemma 4.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Fourier408
import LeanLab.DensityGoldbach.Holder408

open Finset

namespace LeanLab.DensityGoldbach.Stability408

/-- Shao page 13, display 25, raising the Fourier norm bound to q. -/
theorem power_sum_bound {ι : Type*} (s : Finset ι) (a : ι → ℝ) (q M : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hq : 0 < q)
    (h : (∑ i ∈ s, a i ^ q) ^ (1 / q) ≤ M) :
    ∑ i ∈ s, a i ^ q ≤ M ^ q := by
  have hs : 0 ≤ ∑ i ∈ s, a i ^ q := sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) q
  have ht := Real.rpow_le_rpow (Real.rpow_nonneg hs _) h hq.le
  simpa only [one_div, Real.rpow_inv_rpow hs hq.ne'] using ht

/-- Shao page 14, Lemma 4.3. The triangle inequality gives a q norm
bound of 2M for the difference of two Fourier transforms. -/
theorem difference_power_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (q M : ℝ)
    (hq : 1 ≤ q)
    (ha : (∑ i ∈ s, ‖a i‖ ^ q) ^ (1 / q) ≤ M)
    (hb : (∑ i ∈ s, ‖b i‖ ^ q) ^ (1 / q) ≤ M) :
    ∑ i ∈ s, ‖a i - b i‖ ^ q ≤ (2 * M) ^ q := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  apply power_sum_bound s (fun i => ‖a i - b i‖) q (2 * M) (fun i _ => norm_nonneg _) hqpos
  have hsum : (∑ i ∈ s, ‖a i - b i‖ ^ q) ≤ ∑ i ∈ s, (‖a i‖ + ‖b i‖) ^ q := by
    apply sum_le_sum
    intro i _
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le _ _) hqpos.le
  have hmono := Real.rpow_le_rpow
    (sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) hsum (by positivity : 0 ≤ 1 / q)
  have hadd := Real.Lp_add_le_of_nonneg s hq (fun i _ => norm_nonneg (a i))
    (fun i _ => norm_nonneg (b i))
  exact hmono.trans (hadd.trans (by linarith))

/-- Shao page 14, Lemma 4.3. Three telescoping products and Holder
bound the sum of the difference of three Fourier products. -/
theorem product_difference_sum {ι : Type*} (s : Finset ι) (F G : Fin 3 → ι → ℂ)
    (q M ε : ℝ) (hq2 : 2 < q) (hq3 : q < 3) (hM : 0 < M) (hε : 0 ≤ ε)
    (hF : ∀ j, (∑ i ∈ s, ‖F j i‖ ^ q) ^ (1 / q) ≤ M)
    (hG : ∀ j, (∑ i ∈ s, ‖G j i‖ ^ q) ^ (1 / q) ≤ M)
    (hclose : ∀ j i, ‖F j i - G j i‖ ≤ ε) :
    ∑ i ∈ s, ‖F 0 i * F 1 i * F 2 i - G 0 i * G 1 i * G 2 i‖ ≤
      3 * (2 * M) ^ q * ε ^ (3 - q) := by
  have hqpos : 0 < q := by linarith
  have hK : M ^ q ≤ (2 * M) ^ q := Real.rpow_le_rpow hM.le (by linarith) hqpos.le
  have hFs (j : Fin 3) : ∑ i ∈ s, ‖F j i‖ ^ q ≤ (2 * M) ^ q :=
    (power_sum_bound s _ q M (fun i _ => norm_nonneg _) hqpos (hF j)).trans hK
  have hGs (j : Fin 3) : ∑ i ∈ s, ‖G j i‖ ^ q ≤ (2 * M) ^ q :=
    (power_sum_bound s _ q M (fun i _ => norm_nonneg _) hqpos (hG j)).trans hK
  have hDs (j : Fin 3) : ∑ i ∈ s, ‖F j i - G j i‖ ^ q ≤ (2 * M) ^ q :=
    difference_power_sum s _ _ q M (by linarith) (hF j) (hG j)
  have h0 := Holder408.product_sum_le s (fun i => ‖F 1 i‖) (fun i => ‖F 2 i‖)
    (fun i => ‖F 0 i - G 0 i‖) q ε ((2 * M) ^ q) hq2 hq3 hε
    (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
    (fun i _ => hclose 0 i) (hFs 1) (hFs 2) (hDs 0)
  have h1 := Holder408.product_sum_le s (fun i => ‖G 0 i‖) (fun i => ‖F 2 i‖)
    (fun i => ‖F 1 i - G 1 i‖) q ε ((2 * M) ^ q) hq2 hq3 hε
    (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
    (fun i _ => hclose 1 i) (hGs 0) (hFs 2) (hDs 1)
  have h2 := Holder408.product_sum_le s (fun i => ‖G 0 i‖) (fun i => ‖G 1 i‖)
    (fun i => ‖F 2 i - G 2 i‖) q ε ((2 * M) ^ q) hq2 hq3 hε
    (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
    (fun i _ => hclose 2 i) (hGs 0) (hGs 1) (hDs 2)
  have hpoint : ∀ i ∈ s,
      ‖F 0 i * F 1 i * F 2 i - G 0 i * G 1 i * G 2 i‖ ≤
      ‖F 1 i‖ * ‖F 2 i‖ * ‖F 0 i - G 0 i‖ +
      ‖G 0 i‖ * ‖F 2 i‖ * ‖F 1 i - G 1 i‖ +
      ‖G 0 i‖ * ‖G 1 i‖ * ‖F 2 i - G 2 i‖ := by
    intro i _
    have hid : F 0 i * F 1 i * F 2 i - G 0 i * G 1 i * G 2 i =
        F 1 i * F 2 i * (F 0 i - G 0 i) +
        G 0 i * F 2 i * (F 1 i - G 1 i) + G 0 i * G 1 i * (F 2 i - G 2 i) := by ring
    rw [hid]
    have htri := (norm_add_le
      (F 1 i * F 2 i * (F 0 i - G 0 i) + G 0 i * F 2 i * (F 1 i - G 1 i))
      (G 0 i * G 1 i * (F 2 i - G 2 i))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    simpa only [norm_mul] using htri
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_add_distrib] at hsum
  linarith

/-- Shao page 14, Lemma 4.3 with an explicit constant. -/
theorem triple_stability {N : ℕ} [NeZero N] (q M ε : ℝ)
    (hq2 : 2 < q) (hq3 : q < 3) (hM : 0 < M) (hε : 0 < ε)
    (f g : Fin 3 → ZMod N → ℝ)
    (hf : ∀ i, (∑ r, ‖fourierZN N (f i) r‖ ^ q) ^ (1 / q) ≤ M)
    (hg : ∀ i, (∑ r, ‖fourierZN N (g i) r‖ ^ q) ^ (1 / q) ≤ M)
    (hclose : ∀ i r, ‖fourierZN N (f i) r - fourierZN N (g i) r‖ ≤ ε)
    (x : ZMod N) :
    |(∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z)) -
      (∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z))| ≤
      3 * (2 * M) ^ q * ε ^ (3 - q) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hi1 := Fourier408.triple_inversion (f 0) (f 1) (f 2) x
  have hi2 := Fourier408.triple_inversion (g 0) (g 1) (g 2) x
  have hsum := product_difference_sum univ (fun i r => fourierZN N (f i) r)
    (fun i r => fourierZN N (g i) r) q M ε hq2 hq3 hM hε.le hf hg hclose
  have hid : (((∑ y : ZMod N, ∑ z : ZMod N, f 0 y * f 1 z * f 2 (x - y - z)) -
      (∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z)) : ℝ) : ℂ) =
      (1 / (N : ℂ)) * ∑ r : ZMod N,
        (fourierZN N (f 0) r * fourierZN N (f 1) r * fourierZN N (f 2) r -
        fourierZN N (g 0) r * fourierZN N (g 1) r * fourierZN N (g 2) r) *
        ZMod.stdAddChar (-(r * x)) := by
    rw [Complex.ofReal_sub, hi1, hi2, ← mul_sub, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro r _
    ring
  have hnorm := congrArg norm hid
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_div, norm_one,
    Complex.norm_natCast] at hnorm
  rw [hnorm, div_mul_eq_mul_div, one_mul]
  apply div_le_div_of_nonneg_right _ hNpos.le
  apply (norm_sum_le _ _).trans
  calc
    (∑ r : ZMod N, ‖(fourierZN N (f 0) r * fourierZN N (f 1) r * fourierZN N (f 2) r -
      fourierZN N (g 0) r * fourierZN N (g 1) r * fourierZN N (g 2) r) *
      ZMod.stdAddChar (-(r * x))‖) =
      ∑ r : ZMod N, ‖fourierZN N (f 0) r * fourierZN N (f 1) r * fourierZN N (f 2) r -
      fourierZN N (g 0) r * fourierZN N (g 1) r * fourierZN N (g 2) r‖ := by
        apply sum_congr rfl
        intro r _
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
    _ ≤ _ := hsum

end LeanLab.DensityGoldbach.Stability408

#print axioms LeanLab.DensityGoldbach.Stability408.power_sum_bound
#print axioms LeanLab.DensityGoldbach.Stability408.difference_power_sum
#print axioms LeanLab.DensityGoldbach.Stability408.product_difference_sum
#print axioms LeanLab.DensityGoldbach.Stability408.triple_stability
