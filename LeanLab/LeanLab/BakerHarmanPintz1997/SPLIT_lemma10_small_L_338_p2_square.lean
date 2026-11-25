/-
Second split for `leaf_338_fourth_N` in SPLIT_lemma10_small_L_338, P0069 page 24.
The paper bounds ||N||_4 = ||N^2||_2^(1/2) and applies Lemma 1 to the polynomial N^2 of length N^2,
whose coefficients satisfy (3.1) with a larger B. Here:
the square polynomial `DP.sqP2` as a Dirichlet convolution, its value is the square, PROVED;
its length is N^2 with constants c1^2, c2^2, PROVED; its coefficients satisfy (3.1) with
1 + 2 max(B, 0), PROVED; ||N||_4 = ||N^2||_2^(1/2), PROVED.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_large_L_p2_meansq

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- Page 24, the polynomial N^2: coefficient b(n) = sum over a(m) a(m') with m m' = n, support the
products of two support points. -/
noncomputable def DP.sqP2 (P : DP) : DP where
  coef := fun n => ∑ p ∈ (P.supp ×ˢ P.supp).filter (fun p => p.1 * p.2 = n), P.coef p.1 * P.coef p.2
  supp := (P.supp ×ˢ P.supp).image (fun p => p.1 * p.2)

/-- LEAF: page 24, N(s, chi)^2 is the polynomial N^2, the value of `DP.sqP2` is the square. EASY.
PROVED. -/
theorem sqP2_eval (P : DP) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    P.sqP2.eval χ s = P.eval χ s ^ 2 := by
  classical
  unfold DP.eval DP.sqP2
  simp only
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2)
    (t := (P.supp ×ˢ P.supp).image (fun p => p.1 * p.2))
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨-, he⟩ := Finset.mem_filter.mp hp
  subst he
  push_cast
  rw [map_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- LEAF: page 24, N^2 has length N^2: support in (c1^2 N^2, c2^2 N^2). EASY. PROVED. -/
theorem sqP2_hasLen (P : DP) (F c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hlen : P.HasLen F c1 c2) :
    P.sqP2.HasLen (F ^ 2) (c1 ^ 2) (c2 ^ 2) := by
  intro n hn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨a1, b1⟩ := hlen _ hp1
  obtain ⟨a2, b2⟩ := hlen _ hp2
  have h0 : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ p.2 := Nat.cast_nonneg _
  have hF : 0 < F := by
    by_contra hF
    push_neg at hF
    have : c2 * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2.le hF
    linarith
  have hcF : 0 ≤ c1 * F := (mul_pos hc1 hF).le
  push_cast
  constructor
  · have := mul_lt_mul'' a1 a2 hcF hcF
    nlinarith
  · have := mul_lt_mul'' b1 b2 h0 h0'
    nlinarith

/-- LEAF: page 24, the coefficients of N^2 satisfy (3.1) with B'' = 1 + 2 max(B, 0):
|b(n)| <= tau(n) max_{d | n} tau(d)^(2B). EASY. PROVED. -/
theorem sqP2_coef (P : DP) (F c1 c2 B : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) (hlen : P.HasLen F c1 c2)
    (hcoef : P.Coef31 B) : P.sqP2.Coef31 (1 + 2 * max B 0) := by
  classical
  intro n hn
  obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hn
  set n := p0.1 * p0.2 with hndef
  have hpos : ∀ m ∈ P.supp, 0 < m := by
    intro m hm
    obtain ⟨a, b⟩ := hlen m hm
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hF : 0 < F := by
      by_contra hF
      push_neg at hF
      have : c2 * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2.le hF
      linarith
    have : (0 : ℝ) < m := lt_of_le_of_lt (mul_pos hc1 hF).le a
    exact_mod_cast this
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hp0
  have hn0 : n ≠ 0 := Nat.mul_ne_zero (hpos _ hq1).ne' (hpos _ hq2).ne'
  have htau : tau n = (n.divisors.card : ℝ) := by
    simp [tau, ArithmeticFunction.sigma_zero_apply]
  have hτ1 : (1 : ℝ) ≤ n.divisors.card := by
    have : 1 ≤ n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) ≤ n.divisors.card := by linarith
  set β := max B 0
  -- each factor
  have hfac : ∀ m ∈ P.supp, m ∣ n → ‖P.coef m‖ ≤ (n.divisors.card : ℝ) ^ β := by
    intro m hm hdvd
    have hm0 := hpos m hm
    have htm : tau m = (m.divisors.card : ℝ) := by
      simp [tau, ArithmeticFunction.sigma_zero_apply]
    have hm1 : (1 : ℝ) ≤ m.divisors.card := by
      have : 1 ≤ m.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm0.ne'⟩
      exact_mod_cast this
    have hle : (m.divisors.card : ℝ) ≤ n.divisors.card := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn0 hdvd)
    calc ‖P.coef m‖ ≤ tau m ^ B := hcoef m hm
      _ = (m.divisors.card : ℝ) ^ B := by rw [htm]
      _ ≤ (m.divisors.card : ℝ) ^ β := Real.rpow_le_rpow_of_exponent_le hm1 (le_max_left _ _)
      _ ≤ (n.divisors.card : ℝ) ^ β :=
          Real.rpow_le_rpow (by linarith) hle (le_max_right _ _)
  set s := (P.supp ×ˢ P.supp).filter (fun p => p.1 * p.2 = n) with hs
  have hcard : (s.card : ℝ) ≤ n.divisors.card := by
    have : s.card ≤ n.divisors.card := by
      apply Finset.card_le_card_of_injOn (fun p => p.1)
      · intro p hp
        obtain ⟨-, he⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_divisors.mpr ⟨⟨p.2, he.symm⟩, hn0⟩
      · intro p hp p' hp' h
        obtain ⟨hpp, he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp', he'⟩ := Finset.mem_filter.mp hp'
        have h1 : p.1 = p'.1 := h
        have hp10 : 0 < p.1 := hpos _ (Finset.mem_product.mp hpp).1
        have h2 : p.2 = p'.2 := by
          have : p.1 * p.2 = p.1 * p'.2 := by rw [he, h1, he']
          exact Nat.eq_of_mul_eq_mul_left hp10 this
        exact Prod.ext h1 h2
    exact_mod_cast this
  have hβ0 : 0 ≤ (n.divisors.card : ℝ) ^ β := Real.rpow_nonneg hτ0 _
  show ‖∑ p ∈ s, P.coef p.1 * P.coef p.2‖ ≤ tau n ^ (1 + 2 * β)
  calc ‖∑ p ∈ s, P.coef p.1 * P.coef p.2‖ ≤ ∑ p ∈ s, ‖P.coef p.1 * P.coef p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, (n.divisors.card : ℝ) ^ β * (n.divisors.card : ℝ) ^ β := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpp, he⟩ := Finset.mem_filter.mp hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpp
        rw [norm_mul]
        exact mul_le_mul (hfac _ h1 ⟨p.2, he.symm⟩) (hfac _ h2 ⟨p.1, by rw [← he]; ring⟩)
          (norm_nonneg _) hβ0
    _ = s.card * ((n.divisors.card : ℝ) ^ β * (n.divisors.card : ℝ) ^ β) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ β * (n.divisors.card : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hβ0 hβ0)
    _ = tau n ^ (1 + 2 * β) := by
        rw [htau, Real.rpow_add (by linarith), Real.rpow_one, two_mul,
          Real.rpow_add (by linarith)]

/-- LEAF: page 24, ||N||_4 = ||N^2||_2^(1/2). EASY. PROVED. -/
theorem pnorm4_eq_sqP2 (P : DP) (c : Cfg) :
    pnorm P c 4 = pnorm P.sqP2 c 2 ^ (1 / 2 : ℝ) := by
  unfold pnorm
  have hS : ∀ e ∈ c.S, ‖P.sqP2.eval e.2 (half e.1)‖ ^ (2 : ℝ) =
      ‖P.eval e.2 (half e.1)‖ ^ (4 : ℝ) := by
    intro e he
    rw [sqP2_eval, norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [Finset.sum_congr rfl hS, ← Real.rpow_mul
    (sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)]
  norm_num

#print axioms sqP2_eval
#print axioms sqP2_hasLen
#print axioms sqP2_coef
#print axioms pnorm4_eq_sqP2

end LeanLab.BakerHarmanPintz1997
