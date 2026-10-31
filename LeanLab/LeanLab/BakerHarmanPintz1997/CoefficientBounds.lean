/-
P0069, pages 11 and 26, coefficient bounds for the truncated convolution and its error.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Decomp1518
open Finset ArithmeticFunction
namespace LeanLab.BakerHarmanPintz1997
open LeanLab.BakerHarmanPintz1997.Decomp1518
attribute [local instance] Classical.propDecidable
/-- Divisor bounded coefficients stay divisor bounded after the grouping in 4.7. -/
theorem weighted_conv2_norm_le_tau (a b g : ℕ → ℂ) (M N B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ tau n ^ C)
    {k : ℕ} (hk : 0 < k) :
    ‖∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then a m * b n * g (k / (m * n)) else 0‖ ≤ tau k ^ (2 * B + C + 2) := by
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
  have hterm : ∀ u ∈ S, ‖a u.1 * b u.2 * g (k / (u.1 * u.2))‖ ≤ tau k ^ (B + B + C) := by
    intro u hu
    have hd := mem_product.mp (hsub hu)
    have ham : ‖a u.1‖ ≤ tau k ^ B :=
      (ha _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.1).1) hB)
    have hbn : ‖b u.2‖ ≤ tau k ^ B :=
      (hb _).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ (Nat.mem_divisors.mp hd.2).1) hB)
    have hdk : u.1 * u.2 ∣ k := (mem_filter.mp hu).2
    have hqk : k / (u.1 * u.2) ∣ k := Nat.div_dvd_of_dvd hdk
    have hq0 : 0 < k / (u.1 * u.2) := by
      apply Nat.div_pos (Nat.le_of_dvd hk hdk)
      have : u.1 * u.2 ≠ 0 := by intro he; simp [he] at hdk; omega
      omega
    have hgn : ‖g (k / (u.1 * u.2))‖ ≤ tau k ^ C :=
      (hg _ hq0).trans (Real.rpow_le_rpow (by simp [tau]) (htau _ hqk) hC)
    rw [norm_mul, norm_mul, Real.rpow_add htpos, Real.rpow_add htpos]
    exact mul_le_mul (mul_le_mul ham hbn (norm_nonneg _) (Real.rpow_nonneg htpos.le _))
      hgn (norm_nonneg _) (by positivity)
  have heq : (∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then a m * b n * g (k / (m * n)) else 0) = ∑ u ∈ S, a u.1 * b u.2 * g (k / (u.1 * u.2)) := by
    simp [S, sum_filter, sum_product]
  rw [heq]
  calc _ ≤ ∑ u ∈ S, ‖a u.1 * b u.2 * g (k / (u.1 * u.2))‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ S, tau k ^ (B + B + C) := sum_le_sum hterm
    _ ≤ ∑ u ∈ k.divisors ×ˢ k.divisors, tau k ^ (B + B + C) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.rpow_nonneg htpos.le _)
    _ = tau k ^ 2 * tau k ^ (B + B + C) := by
      simp [tau, sigma_zero_apply, pow_two]
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add htpos]
      congr 1
      ring

/-- The truncated Moebius sum has norm bounded by the divisor count. -/
theorem psiTrunc_norm_le_tau (l : ℕ) (hl : 0 < l) (w γ : ℝ) : ‖psiTrunc l w γ‖ ≤ tau l := by
  have hmu : ∀ d : ℕ, ‖(moebius d : ℂ)‖ ≤ 1 := by
    intro d
    exact_mod_cast (abs_moebius_le_one (n := d))
  have hsub : (siftingProduct w).divisors.filter (fun d => d ∣ l ∧ (d : ℝ) < γ) ⊆ l.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2.1, hl.ne'⟩
  unfold psiTrunc
  calc _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, ‖(moebius d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ (siftingProduct w).divisors with d ∣ l ∧ (d : ℝ) < γ, (1 : ℝ) := sum_le_sum (fun d _ => hmu d)
    _ ≤ ∑ d ∈ l.divisors, (1 : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = _ := by simp [tau, sigma_zero_apply]
/-- The boundary error count is bounded by the divisor count. -/
theorem psiErr_le_tau (l : ℕ) (hl : 0 < l) (w γ : ℝ) : psiErr l w γ ≤ tau l := by
  have hsub : (siftingProduct w).divisors.filter
      (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w) ⊆ l.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2.1, hl.ne'⟩
  simpa only [psiErr, tau, sigma_zero_apply] using
    (show (((siftingProduct w).divisors.filter
      (fun d => d ∣ l ∧ γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) ≤ (l.divisors.card : ℝ) by
        exact_mod_cast card_le_card hsub)

/-- The truncated coefficients c prime satisfy a divisor bound of the form 3.1. -/
theorem conv2T_norm_le_tau (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B)
    {k : ℕ} (hk : 0 < k) : ‖conv2T a b M N w γ k‖ ≤ tau k ^ (2 * B + 3) := by
  have hg : ∀ l, 0 < l → ‖psiTrunc l w γ‖ ≤ tau l ^ (1 : ℝ) := by
    intro l hl
    simpa only [Real.rpow_one] using psiTrunc_norm_le_tau l hl w γ
  simpa only [conv2T, show 2 * B + 1 + 2 = 2 * B + 3 by ring] using
    weighted_conv2_norm_le_tau a b (fun l => psiTrunc l w γ) M N B 1 hB (by norm_num) ha hb hg hk
/-- The error majorant c double prime satisfies a divisor bound of the form 3.1. -/
theorem conv2E_le_tau (a b : ℕ → ℂ) (M N w γ B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ n, ‖a n‖ ≤ tau n ^ B) (hb : ∀ n, ‖b n‖ ≤ tau n ^ B)
    {k : ℕ} (hk : 0 < k) : conv2E a b M N w γ k ≤ tau k ^ (2 * B + 3) := by
  have he0 : 0 ≤ conv2E a b M N w γ k := by
    unfold conv2E
    apply sum_nonneg
    intro m hm
    apply sum_nonneg
    intro n hn
    split_ifs
    · unfold psiErr
      positivity
    · positivity
  have ha' : ∀ n, ‖(‖a n‖ : ℂ)‖ ≤ tau n ^ B := by simpa using ha
  have hb' : ∀ n, ‖(‖b n‖ : ℂ)‖ ≤ tau n ^ B := by simpa using hb
  have hg : ∀ l, 0 < l → ‖(psiErr l w γ : ℂ)‖ ≤ tau l ^ (1 : ℝ) := by
    intro l hl
    rw [Complex.norm_of_nonneg (by unfold psiErr; positivity), Real.rpow_one]
    exact psiErr_le_tau l hl w γ
  have h := weighted_conv2_norm_le_tau (fun n => (‖a n‖ : ℂ)) (fun n => (‖b n‖ : ℂ))
    (fun l => (psiErr l w γ : ℂ)) M N B 1 hB (by norm_num) ha' hb' hg hk
  have heq : (∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, ∑ n ∈ Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      if m * n ∣ k then (‖a m‖ : ℂ) * (‖b n‖ : ℂ) * (psiErr (k / (m * n)) w γ : ℂ) else 0) =
      (conv2E a b M N w γ k : ℂ) := by
    simp only [conv2E, Complex.ofReal_sum]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    split_ifs <;> push_cast <;> rfl
  rw [heq, Complex.norm_of_nonneg he0] at h
  simpa only [show 2 * B + 1 + 2 = 2 * B + 3 by ring] using h

#print axioms conv2T_norm_le_tau
#print axioms conv2E_le_tau
#print axioms psiTrunc_norm_le_tau
#print axioms psiErr_le_tau
#print axioms weighted_conv2_norm_le_tau
end LeanLab.BakerHarmanPintz1997
