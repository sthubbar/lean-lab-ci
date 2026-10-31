/-
P0069, page 30, remaining elementary ranges in the proof of Lemma 13.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp1518
namespace LeanLab.BakerHarmanPintz1997
open Finset ArithmeticFunction
open LeanLab.BakerHarmanPintz1997.Decomp1518
attribute [local instance] Classical.propDecidable
/-- The remaining cofactor ranges in the proof of Lemma 13 on page 30. -/
theorem e2_cofactor_ranges {x : ℝ} {m n p h : ℕ} (hx : 1 ≤ x) (hm : x ^ (0.4 : ℝ) < m)
    (hp : x ^ (0.225 : ℝ) < p) (hn : 1 ≤ n) (hk : ((m * n * p * h : ℕ) : ℝ) ≤ x) (hh : 2 ≤ h)
    (hr : Rough h p) : p ≤ h ∧ (h : ℝ) < x ^ (0.375 : ℝ) ∧
      ((n * p : ℕ) : ℝ) < x ^ (0.375 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hm0 : 0 < (m : ℝ) := (Real.rpow_pos_of_pos hx0 _).trans hm
  have hp0 : 0 < (p : ℝ) := (Real.rpow_pos_of_pos hx0 _).trans hp
  have hprime := e2_cofactor_prime hx hm hp hn hk hh hr
  have hph : (p : ℝ) ≤ h := by
    by_contra hlt
    exact hr h hprime (lt_of_not_ge hlt) (dvd_refl h)
  have hmn : (m : ℝ) * p * h ≤ (m : ℝ) * n * p * h := by
    calc (m : ℝ) * p * h = (m : ℝ) * 1 * p * h := by ring
      _ ≤ _ := by gcongr; exact_mod_cast hn
  push_cast at hk
  have hmp : x ^ (0.625 : ℝ) < (m : ℝ) * p := by
    rw [show (0.625 : ℝ) = 0.4 + 0.225 by norm_num, Real.rpow_add hx0]
    gcongr
  have hprod : x ^ (0.625 : ℝ) * x ^ (0.375 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hr0 : 0 < x ^ (0.375 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hmh : x ^ (0.625 : ℝ) < (m : ℝ) * h :=
    hmp.trans_le (mul_le_mul_of_nonneg_left hph hm0.le)
  refine ⟨by exact_mod_cast hph, ?_, ?_⟩
  · by_contra hhx
    have hxl : x ^ (0.375 : ℝ) ≤ h := le_of_not_gt hhx
    have h1 := mul_lt_mul_of_pos_right hmp hr0
    have h2 := mul_le_mul_of_nonneg_left hxl (mul_pos hm0 hp0).le
    nlinarith
  · by_contra hnpx
    have hxl : x ^ (0.375 : ℝ) ≤ (n : ℝ) * p := by simpa using le_of_not_gt hnpx
    have h1 := mul_lt_mul_of_pos_right hmh hr0
    have h2 := mul_le_mul_of_nonneg_left hxl (mul_nonneg hm0.le (Nat.cast_nonneg h))
    nlinarith

/-- Equation 3.1 is preserved by the convolution 4.7 after increasing its exponent. -/
theorem conv2_norm_le_tau (a b : ℕ → ℂ) (M N z B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B)
    {k : ℕ} (hk : 0 < k) : ‖conv2 a b M N z k‖ ≤ tau k ^ (2 * B + 2) := by
  let S := (Ioc ⌊M⌋₊ ⌊2 * M⌋₊ ×ˢ Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
    (fun u : ℕ × ℕ => u.1 * u.2 ∣ k)
  have hsub : S ⊆ k.divisors ×ˢ k.divisors := by
    intro u hu
    have hd := (mem_filter.mp hu).2
    apply mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨(dvd_mul_right u.1 u.2).trans hd, hk.ne'⟩,
      Nat.mem_divisors.mpr ⟨(dvd_mul_left u.2 u.1).trans hd, hk.ne'⟩⟩
  have htau : ∀ d, d ∣ k → tau d ≤ tau k := by
    intro d hd
    simp only [tau, sigma_zero_apply]
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hk.ne' hd)
  have htpos : 0 < tau k := by
    simp only [tau, sigma_zero_apply, Nat.cast_pos]
    exact card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne'⟩
  have hpsi : ∀ l, ‖psi l z‖ ≤ 1 := by
    intro l
    unfold psi
    split_ifs <;> norm_num
  have hterm : ∀ u ∈ S, ‖a u.1 * b u.2 * psi (k / (u.1 * u.2)) z‖ ≤ tau k ^ (B + B) := by
    intro u hu
    have hd := mem_product.mp (hsub hu)
    have ham : ‖a u.1‖ ≤ tau k ^ B :=
      (ha _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.1).1) hB)
    have hbn : ‖b u.2‖ ≤ tau k ^ B :=
      (hb _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.2).1) hB)
    rw [norm_mul, norm_mul, Real.rpow_add htpos]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hpsi _)).trans
      (mul_le_mul ham hbn (norm_nonneg _) (Real.rpow_nonneg htpos.le _))
  have heq : conv2 a b M N z k = ∑ u ∈ S, a u.1 * b u.2 * psi (k / (u.1 * u.2)) z := by
    simp [conv2, S, sum_filter, sum_product]
  rw [heq]
  calc _ ≤ ∑ u ∈ S, ‖a u.1 * b u.2 * psi (k / (u.1 * u.2)) z‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S, tau k ^ (B + B) := sum_le_sum hterm
    _ ≤ ∑ u ∈ k.divisors ×ˢ k.divisors, tau k ^ (B + B) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.rpow_nonneg htpos.le _)
    _ = tau k ^ 2 * tau k ^ (B + B) := by
      simp [tau, sigma_zero_apply, pow_two]
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
      congr 1
      ring

/-- The interval I on page 1 has width 2Y up to the two floor errors. -/
theorem Iset_card_bounds {ε x : ℝ} (hY : 0 ≤ Yof ε x) (hx : 2 * Yof ε x ≤ x) :
    2 * Yof ε x - 1 ≤ ((Iset ε x).card : ℝ) ∧
      ((Iset ε x).card : ℝ) ≤ 2 * Yof ε x + 1 := by
  have hx0 : 0 ≤ x := by linarith
  have hlo : 0 ≤ x - 2 * Yof ε x := by linarith
  have hm : ⌊x - 2 * Yof ε x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
  simp only [Iset, Nat.card_Ioc, Nat.cast_sub hm]
  constructor <;> linarith [Nat.floor_le hx0, Nat.floor_le hlo,
    Nat.lt_floor_add_one x, Nat.lt_floor_add_one (x - 2 * Yof ε x)]

/-- The three elementary ratios after equation 4.20, with H standing for Nh. -/
theorem lemma13_large_prime_ranges {x M H p : ℝ} (hx : 0 < x) (hM : 0 < M) (hp : 0 < p)
    (hMlo : x ^ (0.4 : ℝ) ≤ M) (hMhi : M ≤ x ^ (0.46 : ℝ))
    (hH : x ^ (0.46 : ℝ) ≤ H) (hcut : x ^ (0.9 : ℝ) ≤ M ^ 2 * p)
    (hprod : M * p * H ≤ x) :
    p ≤ x ^ (0.14 : ℝ) ∧ M / H ≤ 1 ∧ H / M ≤ x ^ (0.1 : ℝ) := by
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hx _).trans_le hH
  have hMH : x ^ (0.86 : ℝ) ≤ M * H := by
    calc
      x ^ (0.86 : ℝ) = x ^ (0.4 : ℝ) * x ^ (0.46 : ℝ) := by
        rw [← Real.rpow_add hx]; norm_num
      _ ≤ M * H := mul_le_mul hMlo hH (Real.rpow_nonneg hx.le _) hM.le
  have hpbound : p ≤ x / (M * H) := by
    apply (le_div_iff₀ (mul_pos hM hH0)).mpr
    nlinarith
  have hratio : H / M ≤ x / (M ^ 2 * p) := by
    apply (div_le_div_iff₀ hM (mul_pos (sq_pos_of_pos hM) hp)).mpr
    convert mul_le_mul_of_nonneg_right hprod hM.le using 1 <;> ring
  refine ⟨?_, (div_le_one hH0).mpr (hMhi.trans hH), ?_⟩
  · calc p ≤ x / (M * H) := hpbound
      _ ≤ x / x ^ (0.86 : ℝ) := div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos hx _) hMH
      _ = x ^ (0.14 : ℝ) := by
        nth_rw 1 [← Real.rpow_one x]
        rw [← Real.rpow_sub hx]
        norm_num
  · calc H / M ≤ x / (M ^ 2 * p) := hratio
      _ ≤ x / x ^ (0.9 : ℝ) := div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos hx _) hcut
      _ = x ^ (0.1 : ℝ) := by
        nth_rw 1 [← Real.rpow_one x]
        rw [← Real.rpow_sub hx]
        norm_num

#print axioms lemma13_large_prime_ranges
#print axioms Iset_card_bounds
#print axioms conv2_norm_le_tau
#print axioms e2_cofactor_ranges
end LeanLab.BakerHarmanPintz1997
