import LeanLab.LanguascoPerelli1996.Parameter318

/-!
Derived adjacent parameter bounds for P0071 page 360 display 25.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Parameter318b
open Real ArithmeticFunction Parameter318

/-- Page 360 display 25, derived absolute weighted coefficient sum estimate. -/
theorem lambda_weighted_sum_bound {K : ℝ} (hK : 1 ≤ K) :
    Summable (fun n : ℕ => (n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K)) ∧
      (∑' n : ℕ, (n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K)) ≤
        20 * K ^ 2 * Real.sqrt K := by
  have hK0 : 0 < K := by linarith
  let r := Real.exp (-1 / K)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hK0)
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
    (hasSum_sq_mul_geometric_of_norm_lt_one hr).summable
  let g := fun n : ℕ => Real.sqrt K * ((n : ℝ) * r ^ n) + ((n : ℝ) ^ 2 * r ^ n) / Real.sqrt K
  have hg : Summable g := (h1.mul_left _).add (h2.div_const _)
  have hexp (n : ℕ) : Real.exp (-(n : ℝ) / K) = r ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp (n : ℕ) : (n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K) ≤ g n := by
    rw [hexp]
    convert mul_le_mul_of_nonneg_right (lambda_mul_le hK0 n) (pow_nonneg (Real.exp_pos _).le n) using 1 <;> ring
  have hf : Summable (fun n : ℕ => (n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K)) :=
    hg.of_nonneg_of_le (fun n => by positivity) hp
  refine ⟨hf, (hf.tsum_le_tsum hp hg).trans ?_⟩
  change (∑' n : ℕ, (Real.sqrt K * ((n : ℝ) * r ^ n) + ((n : ℝ) ^ 2 * r ^ n) / Real.sqrt K)) ≤ _
  rw [(h1.mul_left _).tsum_add (h2.div_const _), tsum_mul_left, tsum_div_const]
  obtain ⟨hb1, hb2⟩ := geometric_moments_bound hK
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  calc
    _ ≤ Real.sqrt K * (4 * K ^ 2) + (16 * K ^ 3) / Real.sqrt K :=
      add_le_add (mul_le_mul_of_nonneg_left hb1 hs.le) (div_le_div_of_nonneg_right hb2 hs.le)
    _ = 20 * K ^ 2 * Real.sqrt K := by
      field_simp
      nlinarith [Real.sq_sqrt hK0.le]

/-- Page 360 display 25, derived absolute difference bound before rounding N. -/
theorem dampedSum_difference_le {N K : ℝ} (hN : 0 < N) (hNK : N ≤ K) (hK : 1 ≤ K)
    (η : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖Section5108.dampedSum N η χ - Section5108.dampedSum K η χ‖ ≤
      (N⁻¹ - K⁻¹) * (20 * K ^ 2 * Real.sqrt K) := by
  have hK0 : 0 < K := hN.trans_le hNK
  have hδ : 0 ≤ N⁻¹ - K⁻¹ := sub_nonneg.mpr (inv_anti₀ hN hNK)
  obtain ⟨hs, hsum⟩ := lambda_weighted_sum_bound hK
  have he (x : ℝ) : ‖e x‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  let f := fun A : ℝ => fun n : ℕ =>
    (Λ n : ℂ) * χ (n : ZMod q) * (Real.exp (-(n : ℝ) / A) : ℂ) * e ((n : ℝ) * η)
  have hsn : Summable (f N) := Section5108.dampedSum_summable hN η χ
  have hsk : Summable (f K) := Section5108.dampedSum_summable hK0 η χ
  have hbound (n : ℕ) : ‖f N n - f K n‖ ≤
      (N⁻¹ - K⁻¹) * ((n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K)) := by
    obtain ⟨hpos, hdiff⟩ := damping_difference_le hN hNK n
    have hf : f N n - f K n =
        (Λ n : ℂ) * χ (n : ZMod q) *
          ((Real.exp (-(n : ℝ) / N) - Real.exp (-(n : ℝ) / K) : ℝ) : ℂ) * e ((n : ℝ) * η) := by
      dsimp only [f]
      push_cast
      ring
    rw [hf, norm_mul, norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_nonneg (n := n)),
      abs_sub_comm, abs_of_nonneg hpos]
    have hc : Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one _) (vonMangoldt_nonneg (n := n))
    calc
      _ ≤ Λ n * (Real.exp (-(n : ℝ) / K) - Real.exp (-(n : ℝ) / N)) :=
        mul_le_mul_of_nonneg_right hc hpos
      _ ≤ Λ n * ((N⁻¹ - K⁻¹) * (n : ℝ) * Real.exp (-(n : ℝ) / K)) :=
        mul_le_mul_of_nonneg_left hdiff (vonMangoldt_nonneg (n := n))
      _ = _ := by ring
  have hnorm : Summable (fun n => ‖f N n - f K n‖) :=
    (hs.mul_left (N⁻¹ - K⁻¹)).of_nonneg_of_le (fun n => norm_nonneg _) hbound
  have hsumdiff : ‖∑' n, (f N n - f K n)‖ ≤
      (N⁻¹ - K⁻¹) * ∑' n : ℕ, (n : ℝ) * Λ n * Real.exp (-(n : ℝ) / K) := by
    refine (norm_tsum_le_tsum_norm hnorm).trans ?_
    rw [← tsum_mul_left]
    exact hnorm.tsum_le_tsum hbound (hs.mul_left _)
  unfold Section5108.dampedSum
  change ‖∑' n, f N n - ∑' n, f K n‖ ≤ _
  rw [← hsn.tsum_sub hsk]
  exact hsumdiff.trans (mul_le_mul_of_nonneg_left hsum hδ)

/-- Page 360 display 25, derived uniform adjacent damping parameter comparison. -/
theorem dampedSum_adjacent_le {N K : ℝ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKN : K ≤ N + 1)
    (η : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖Section5108.dampedSum N η χ - Section5108.dampedSum K η χ‖ ≤ 80 * Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := hN0.trans_le hNK
  have hK1 : 1 ≤ K := hN.trans hNK
  have hK2 : K ≤ 2 * N := by linarith
  have hδ : 0 ≤ N⁻¹ - K⁻¹ := sub_nonneg.mpr (inv_anti₀ hN0 hNK)
  have hid : (N⁻¹ - K⁻¹) * K ^ 2 = (K - N) * K / N := by field_simp <;> ring
  have hg : (N⁻¹ - K⁻¹) * K ^ 2 ≤ 2 := by
    rw [hid]
    apply (div_le_iff₀ hN0).2
    have hh := mul_le_mul_of_nonneg_right (show K - N ≤ 1 by linarith) hK0.le
    nlinarith
  have hs : Real.sqrt K ≤ 2 * Real.sqrt N := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt N)).2
    nlinarith [Real.sq_sqrt hN0.le]
  calc
    _ ≤ (N⁻¹ - K⁻¹) * (20 * K ^ 2 * Real.sqrt K) := dampedSum_difference_le hN0 hNK hK1 η χ
    _ = 20 * ((N⁻¹ - K⁻¹) * K ^ 2) * Real.sqrt K := by ring
    _ ≤ 20 * 2 * Real.sqrt K := by gcongr
    _ ≤ 80 * Real.sqrt N := by nlinarith

end LeanLab.LanguascoPerelli1996.Parameter318b

#print axioms LeanLab.LanguascoPerelli1996.Parameter318b.lambda_weighted_sum_bound
#print axioms LeanLab.LanguascoPerelli1996.Parameter318b.dampedSum_difference_le
#print axioms LeanLab.LanguascoPerelli1996.Parameter318b.dampedSum_adjacent_le
