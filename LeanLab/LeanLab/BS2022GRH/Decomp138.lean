/-
AI wrote this Lean code for CODEX task138, 2026-10-27.
P0021 journal pp. 1221 and 1222, Lemma 7 and displays 6 to 10.
The assembly has the exact sealed conclusion Lemma7J.
The reciprocal prime estimate remains a cited leaf from Lemma 6.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.Lemma8

namespace LeanLab.BS2022GRH.Decomp138
open Real Finset Classical ChenThresholdGRH

/-- The finite prime interval used in Lemma 7, p. 1221. -/
noncomputable def band (u z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z)

/-- The reciprocal square prime tail in display 6, p. 1221. -/
noncomputable def squareTail (u₀ : ℝ) : ℝ :=
  ∑' p : {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2

/-- LEAF. Display 9, p. 1222, from Lemma 6, pp. 1219 to 1221.
CITED inputs are Rosser and Schoenfeld 1962, Theorem 20, and Broadbent et al.,
Table 15, plus the paper's computation up to 10^12.
The strict inequality uses the slack in the rounded constant 1.131e-7. -/
theorem reciprocal_sum_lt (z u : ℝ) (hz : exp 2753 < z) (hu : 400 ≤ u) (huz : u < z) :
    ∑ p ∈ band u z, (1 : ℝ) / p < log (log z) - log (log u) + 1.131e-7 := by
  sorry

/-- LEAF. Display 6, p. 1221. The square prime tail is summable. -/
theorem square_tail_summable (u₀ : ℝ) :
    Summable (fun p : {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)} => 1 / ((p : ℕ) : ℝ) ^ 2) := by
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype _

/-- LEAF. Display 7, p. 1221. The finite square sum is bounded by the tail. -/
theorem square_sum_le_tail (z u₀ u : ℝ) (hu : u₀ ≤ u) :
    ∑ p ∈ band u z, (1 : ℝ) / (p : ℝ) ^ 2 ≤ squareTail u₀ := by
  let f : {p // p ∈ band u z} → {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)} := fun p =>
    ⟨p.1, (mem_filter.mp p.2).2.1, hu.trans (mem_filter.mp p.2).2.2.1⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun p : {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)} => p.1) h)
  have hsum : Summable (fun p : {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)} =>
      1 / ((p : ℕ) : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).subtype _
  let S := (band u z).attach.image f
  have hb := hsum.sum_le_tsum S (fun _ _ => by positivity)
  calc
    ∑ p ∈ band u z, (1 : ℝ) / (p : ℝ) ^ 2 =
        ∑ p ∈ (band u z).attach, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 := (sum_attach _ _).symm
    _ = ∑ p ∈ S, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
      rw [show S = (band u z).attach.image f from rfl,
        sum_image (fun a _ b _ h => hinj h)]
    _ ≤ squareTail u₀ := hb

/-- LEAF. First equality in the proof of Lemma 7, p. 1221. -/
theorem product_split (z u : ℝ) (hu : 400 ≤ u) :
    (∏ p ∈ band u z, (1 - 1 / ((p : ℝ) - 1))⁻¹) =
      (∏ p ∈ band u z, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) *
      ∏ p ∈ band u z, (1 - 1 / (p : ℝ))⁻¹ := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hpu := (mem_filter.mp hp).2.2.1
  exact LeanLab.BS2022GRH.factor (by linarith)

/-- LEAF. First factor estimate and display 7, p. 1221. -/
theorem correction_product_le (z u₀ u : ℝ) (hu₀ : 400 ≤ u₀) (hu : u₀ ≤ u) :
    (∏ p ∈ band u z, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
      exp (u₀ / (u₀ - 2) * squareTail u₀) := by
  have htail := square_sum_le_tail z u₀ u hu
  have hc : 0 ≤ u₀ / (u₀ - 2) := div_nonneg (by linarith) (by linarith)
  calc
    _ ≤ ∏ p ∈ band u z, exp (u₀ / (u₀ - 2) * (1 / (p : ℝ) ^ 2)) := by
      apply prod_le_prod₀
      · intro p hp
        have hpu := (mem_filter.mp hp).2.2.1
        have hp0 : 0 < (p : ℝ) := by linarith
        have hp2 : 0 < (p : ℝ) - 2 := by linarith
        positivity
      · intro p hp
        have hpu := (mem_filter.mp hp).2.2.1
        have hp0 : 0 < (p : ℝ) := by linarith
        have hp2 : 0 < (p : ℝ) - 2 := by linarith
        have hu2 : 0 < u₀ - 2 := by linarith
        have hr : (p : ℝ) / ((p : ℝ) - 2) ≤ u₀ / (u₀ - 2) := by
          apply (div_le_div_iff₀ hp2 hu2).2
          nlinarith
        have heq : 1 / ((p : ℝ) * ((p : ℝ) - 2)) =
            ((p : ℝ) / ((p : ℝ) - 2)) * (1 / (p : ℝ) ^ 2) := by
          field_simp
        calc
          _ ≤ exp (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
            linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 2)))]
          _ ≤ _ := exp_le_exp.mpr (by rw [heq]; exact mul_le_mul_of_nonneg_right hr (by positivity))
    _ = exp (u₀ / (u₀ - 2) * ∑ p ∈ band u z, (1 : ℝ) / (p : ℝ) ^ 2) := by
      rw [← exp_sum, mul_sum]
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_left htail hc)

/-- LEAF. Logarithm estimate before display 10, p. 1222. -/
theorem log_remainder {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 400) :
    -log (1 - x) ≤ x + 0.501 * x ^ 2 := by
  have ht : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le ht 3
  rw [abs_le, abs_of_nonneg hx] at h
  norm_num [Finset.sum_range_succ] at h
  have hr : x ^ 4 / (1 - x) ≤ (0.001 : ℝ) * x ^ 2 - x ^ 3 / 3 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - x)).2
    have hq : x ^ 2 ≤ (1 / 400 : ℝ) * x := by nlinarith
    have hq2 : x ^ 2 ≤ (1 / 160000 : ℝ) := by nlinarith
    have hp : x ^ 2 * ((0.001 : ℝ) - (0.001 + 1 / 3) * x - (2 / 3) * x ^ 2) ≥ 0 := by
      apply mul_nonneg (sq_nonneg x)
      nlinarith
    nlinarith
  linarith [h.1]

/-- LEAF. Display 8 and the logarithm estimate, p. 1222. -/
theorem inverse_product_le (z u : ℝ) (hu : 400 ≤ u) :
    (∏ p ∈ band u z, (1 - 1 / (p : ℝ))⁻¹) ≤
      exp ((∑ p ∈ band u z, (1 : ℝ) / p) +
        0.501 * ∑ p ∈ band u z, (1 : ℝ) / (p : ℝ) ^ 2) := by
  calc
    _ ≤ ∏ p ∈ band u z, exp ((1 : ℝ) / p + 0.501 * ((1 : ℝ) / p) ^ 2) := by
      apply prod_le_prod₀
      · intro p hp
        have hpu := (mem_filter.mp hp).2.2.1
        have hp0 : 0 < (p : ℝ) := by linarith
        have hp1 : 1 / (p : ℝ) < 1 := (div_lt_one hp0).2 (by linarith)
        positivity
      · intro p hp
        have hpu := (mem_filter.mp hp).2.2.1
        have hp0 : 0 < (p : ℝ) := by linarith
        have hp400 : (400 : ℝ) ≤ p := hu.trans hpu
        have hx : (1 : ℝ) / p ≤ 1 / 400 :=
          one_div_le_one_div_of_le (by norm_num) hp400
        have hp1 : 0 < 1 - (1 : ℝ) / p := by linarith
        calc
          _ = exp (-log (1 - (1 : ℝ) / p)) := by rw [exp_neg, exp_log hp1]
          _ ≤ _ := exp_le_exp.mpr (log_remainder (by positivity) hx)
    _ = _ := by
      rw [← exp_sum, sum_add_distrib, ← mul_sum]
      simp only [div_pow, one_pow]

/-- LEAF. Display 10, p. 1222, conditional on the reciprocal sum estimate. -/
theorem mertens_product_lt (z u₀ u : ℝ) (hu₀ : 400 ≤ u₀) (hu : u₀ ≤ u) (huz : u < z)
    (h9 : ∑ p ∈ band u z, (1 : ℝ) / p < log (log z) - log (log u) + 1.131e-7) :
    (∏ p ∈ band u z, (1 - 1 / (p : ℝ))⁻¹) <
      exp (1.131e-7 + 0.501 * squareTail u₀) * (log z / log u) := by
  have hlu : 0 < log u := log_pos (by linarith)
  have hlz : 0 < log z := log_pos (by linarith)
  calc
    _ ≤ exp ((∑ p ∈ band u z, (1 : ℝ) / p) +
        0.501 * ∑ p ∈ band u z, (1 : ℝ) / (p : ℝ) ^ 2) := inverse_product_le z u (hu₀.trans hu)
    _ < exp ((log (log z) - log (log u) + 1.131e-7) + 0.501 * squareTail u₀) := by
      apply exp_lt_exp.mpr
      exact add_lt_add_of_lt_of_le h9 (mul_le_mul_of_nonneg_left
        (square_sum_le_tail z u₀ u hu) (by norm_num))
    _ = _ := by
      rw [show log (log z) - log (log u) + 1.131e-7 + 0.501 * squareTail u₀ =
        (1.131e-7 + 0.501 * squareTail u₀) + (log (log z) - log (log u)) by ring,
        exp_add, exp_sub, exp_log hlz, exp_log hlu]

/-- LEAF. A coarse tail bound for display 6, p. 1221, by the reciprocal telescope. -/
theorem square_tail_le (u₀ : ℝ) (hu₀ : 400 ≤ u₀) : squareTail u₀ ≤ 1 / 399 := by
  apply Real.tsum_le_of_sum_le (fun _ => by positivity)
  intro s
  let N := 401 + s.sup (fun p => p.1)
  have hN : 400 ≤ N := by dsimp [N]; omega
  have hsub : s.image (fun p => (p.1 : ℕ)) ⊆ Ico 400 N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    have hp400 : (400 : ℝ) ≤ p.1 := hu₀.trans p.2.2
    have hp400' : 400 ≤ p.1 := by exact_mod_cast hp400
    have hb := Finset.le_sup (f := fun p : {p : ℕ // p.Prime ∧ u₀ ≤ (p : ℝ)} => p.1) hp
    simp only [mem_Ico]
    dsimp [N]
    omega
  have heq : ∑ p ∈ s, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 =
      ∑ n ∈ s.image (fun p => (p.1 : ℕ)), (1 : ℝ) / (n : ℝ) ^ 2 := by
    rw [sum_image]
    intro a _ b _ h
    exact Subtype.ext h
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Ico 400 N, (1 : ℝ) / (n : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Ico 400 N, (1 : ℝ) / (((n : ℝ) - 1) * (n : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn400 : (400 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      apply one_div_le_one_div_of_le (by nlinarith)
      nlinarith
    _ = 1 / 399 - 1 / ((N : ℝ) - 1) := by rw [tele2 400 (by norm_num) N hN]; norm_num
    _ ≤ 1 / 399 := by
      have hN' : (400 : ℝ) ≤ N := by exact_mod_cast hN
      have : 0 ≤ 1 / ((N : ℝ) - 1) := one_div_nonneg.mpr (by linarith)
      linarith

/-- LEAF. The last inequality of display 6, p. 1221. -/
theorem epsilon_lt (u₀ : ℝ) (hu₀ : 400 ≤ u₀) : epsJ u₀ < 1 / 63 := by
  have hS := square_tail_le u₀ hu₀
  have hS0 : 0 ≤ squareTail u₀ := tsum_nonneg (fun _ => by positivity)
  have hu2 : 0 < u₀ - 2 := by linarith
  have hc : u₀ / (u₀ - 2) + 0.501 ≤ 3 := by
    have : u₀ / (u₀ - 2) ≤ 2 := (div_le_iff₀ hu2).2 (by linarith)
    linarith
  have hx : 1.131e-7 + (u₀ / (u₀ - 2) + 0.501) * squareTail u₀ ≤ 1 / 100 := by
    have h := mul_le_mul hc hS hS0 (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have he : exp (1 / 100 : ℝ) ≤ (1 - (1 / 100 : ℝ))⁻¹ :=
    LeanLab.BS2022GRH.exp_le_inv (by norm_num)
  unfold epsJ
  change exp (1.131e-7 + (u₀ / (u₀ - 2) + 0.501) * squareTail u₀) - 1 < 1 / 63
  have hm := exp_le_exp.mpr hx
  norm_num at he
  linarith

/-- Lemma 7, pp. 1221 and 1222, with the exact sealed conclusion.
CONDITIONAL ON the named reciprocal prime estimate. The assembly has no sorry. -/
theorem lemma7J_of_reciprocal
    (h9 : ∀ z u : ℝ, exp 2753 < z → 400 ≤ u → u < z →
      ∑ p ∈ band u z, (1 : ℝ) / p < log (log z) - log (log u) + 1.131e-7) : Lemma7J := by
  intro z u₀ u hz hu₀ hu huz
  refine ⟨?_, epsilon_lt u₀ hu₀⟩
  change (∏ p ∈ band u z, (1 - 1 / ((p : ℝ) - 1))⁻¹) < _
  rw [product_split z u (hu₀.trans hu)]
  have hnonneg : 0 ≤ ∏ p ∈ band u z, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hpu := (mem_filter.mp hp).2.2.1
    have hp0 : 0 < (p : ℝ) := by linarith
    have hp1 : 1 / (p : ℝ) < 1 := (div_lt_one hp0).2 (by linarith)
    positivity
  calc
    _ ≤ exp (u₀ / (u₀ - 2) * squareTail u₀) *
        ∏ p ∈ band u z, (1 - 1 / (p : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right (correction_product_le z u₀ u hu₀ hu) hnonneg
    _ < exp (u₀ / (u₀ - 2) * squareTail u₀) *
        (exp (1.131e-7 + 0.501 * squareTail u₀) * (log z / log u)) :=
      mul_lt_mul_of_pos_left (mertens_product_lt z u₀ u hu₀ hu huz
        (h9 z u hz (hu₀.trans hu) huz)) (exp_pos _)
    _ = (1 + epsJ u₀) * (log z / log u) := by
      rw [← mul_assoc, ← exp_add]
      unfold epsJ squareTail
      congr 1
      ring_nf

/-- Lemma 7 with display 6, p. 1221. OPEN only at the cited reciprocal sum leaf. -/
theorem lemma7J : Lemma7J := lemma7J_of_reciprocal reciprocal_sum_lt

/-- A nonempty parameter instance for Lemma 7, p. 1221. -/
theorem parameters_nonvacuous : ∃ z u₀ u : ℝ,
    exp 2753 < z ∧ 400 ≤ u₀ ∧ u₀ ≤ u ∧ u < z := by
  refine ⟨exp 2753 + 1, 400, 400, ?_⟩
  have h := Real.add_one_le_exp (2753 : ℝ)
  exact ⟨by linarith, le_rfl, le_rfl, by linarith⟩

end LeanLab.BS2022GRH.Decomp138

#print axioms LeanLab.BS2022GRH.Decomp138.product_split
#print axioms LeanLab.BS2022GRH.Decomp138.lemma7J_of_reciprocal
#print axioms LeanLab.BS2022GRH.Decomp138.lemma7J

#print axioms LeanLab.BS2022GRH.Decomp138.square_tail_summable

#print axioms LeanLab.BS2022GRH.Decomp138.square_sum_le_tail

#print axioms LeanLab.BS2022GRH.Decomp138.correction_product_le

#print axioms LeanLab.BS2022GRH.Decomp138.log_remainder

#print axioms LeanLab.BS2022GRH.Decomp138.inverse_product_le

#print axioms LeanLab.BS2022GRH.Decomp138.mertens_product_lt

#print axioms LeanLab.BS2022GRH.Decomp138.square_tail_le

#print axioms LeanLab.BS2022GRH.Decomp138.epsilon_lt

#print axioms LeanLab.BS2022GRH.Decomp138.parameters_nonvacuous
