/-
Split of the LEAF `mertens_range_product` of SPLIT_premise_of_range into one cited leaf, the sum form
of Mertens' second estimate on a range, with an assembly that has the leaf's statement verbatim and
uses no sorry. The passage from the sum to the product is elementary:
(1 - x)⁻¹ ≤ exp (x (1 + 2x)) for 0 ≤ x ≤ 1/2, then K^{β - 1} exp (β C / log Y) ≤ 1 + ε.
This file adds no definition and changes no existing file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BS2022GRH.SPLIT_premise_of_range

namespace LeanLab.BS2022GRH.SieveAllLevels1611
open Real Finset Classical

/-- LEAF: Mertens' second theorem with explicit error, CITED from Rosser and Schoenfeld 1962,
Theorem 5, as used in step 7 of the hand proof of `fixedKappa_of_allLevels`: for 2 ≤ u < w,
∑_{u ≤ p < w} 1/p ≤ log (log w / log u) + C / log u. From
|∑_{p ≤ x} 1/p - log log x - B| < 1/log² x for x > 1, so C = 2 / log 2 works.
HARD: explicit Mertens is not in Mathlib. Strictly easier than the parent: a sum, no product, no η. -/
theorem mertens_sum_range :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : ℝ, 2 ≤ u → u < w →
      ∑ p ∈ (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w), (1 : ℝ) / p
        ≤ log (log w / log u) + C / log u := by
  sorry

/-- PROVED: (1 - x)⁻¹ ≤ exp (x (1 + 2x)) for 0 ≤ x ≤ 1/2. -/
theorem inv_one_sub_le_exp (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ exp (x * (1 + 2 * x)) := by
  have hpos : 0 < 1 - x := by linarith
  have he : 1 + x * (1 + 2 * x) ≤ exp (x * (1 + 2 * x)) := by
    have := add_one_le_exp (x * (1 + 2 * x)); linarith
  have hk : 1 ≤ (1 + x * (1 + 2 * x)) * (1 - x) := by nlinarith [mul_nonneg h0 h0]
  rw [inv_le_iff_one_le_mul₀' hpos]
  calc (1 : ℝ) ≤ (1 + x * (1 + 2 * x)) * (1 - x) := hk
    _ ≤ exp (x * (1 + 2 * x)) * (1 - x) := by gcongr
    _ = (1 - x) * exp (x * (1 + 2 * x)) := by ring

/-- **Assembly**, CONDITIONAL ON `mertens_sum_range`: the statement of `mertens_range_product`
verbatim. -/
theorem mertens_range_product_split {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ Y : ℝ, 2 ≤ Y ∧ ∀ u w : ℝ, Y ≤ u → u < w → log w ≤ K * log u →
      ∏ p ∈ (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w),
        (1 - (1 + η) / (p : ℝ))⁻¹ ≤ (1 + ε) * (log w / log u) := by
  obtain ⟨C, hC0, hC⟩ := mertens_sum_range
  set K₁ := max K 2 with hK₁
  have hK₁2 : (2 : ℝ) ≤ K₁ := le_max_right K 2
  set L := log K₁ with hL
  have hL0 : 0 < L := log_pos (by linarith)
  set t := log (1 + ε) with ht
  have ht0 : 0 < t := log_pos (by linarith)
  set η := min (1 / 2) (t / (4 * L)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hηh : η ≤ 1 / 2 := min_le_left _ _
  have hηL : η * L ≤ t / 4 := by
    have : η ≤ t / (4 * L) := min_le_right _ _
    calc η * L ≤ t / (4 * L) * L := by gcongr
      _ = t / 4 := by field_simp
  set Y := max (max 4 (24 * L / t + 1)) (exp (6 * C / t + 1)) with hY
  have hY4 : (4 : ℝ) ≤ Y := le_trans (le_max_left _ _) (le_max_left _ _)
  have hYL : 24 * L / t ≤ Y := by
    have : 24 * L / t + 1 ≤ Y := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hYe : exp (6 * C / t + 1) ≤ Y := le_max_right _ _
  have hlogY : 6 * C / t + 1 ≤ log Y := by
    rw [← log_exp (6 * C / t + 1)]; exact log_le_log (exp_pos _) hYe
  refine ⟨η, hη0, by linarith, Y, by linarith, ?_⟩
  intro u w hYu huw hK
  have hu4 : (4 : ℝ) ≤ u := le_trans hY4 hYu
  have hlogu : 0 < log u := log_pos (by linarith)
  have hlogw : log u < log w := log_lt_log (by linarith) huw
  set R := log w / log u with hR
  have hR1 : 1 < R := (one_lt_div hlogu).2 hlogw
  have hRK : R ≤ K := by rw [hR, div_le_iff₀ hlogu]; exact hK
  have hlogR : log R ≤ L := log_le_log (by linarith) (le_trans hRK (le_max_left K 2))
  set c := 2 * (1 + η) / Y with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one (by linarith)]; linarith
  set β := (1 + c) * (1 + η) with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hβ3 : β ≤ 3 := by nlinarith
  set F := (range ⌈w⌉₊).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < w) with hF
  -- factorwise bound
  have hfac : ∀ p ∈ F, (1 - (1 + η) / (p : ℝ))⁻¹ ≤ exp ((1 + η) / (p : ℝ) * (1 + c)) := by
    intro p hp
    simp only [hF, mem_filter] at hp
    have hpu : u ≤ (p : ℝ) := hp.2.2.1
    have hpY : Y ≤ (p : ℝ) := le_trans hYu hpu
    have hp0 : (0 : ℝ) < p := by linarith
    have hx0 : 0 ≤ (1 + η) / (p : ℝ) := by positivity
    have hxY : (1 + η) / (p : ℝ) ≤ (1 + η) / Y := div_le_div_of_nonneg_left (by linarith)
      (by linarith) hpY
    have hxh : (1 + η) / Y ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    refine le_trans (inv_one_sub_le_exp _ hx0 (by linarith)) (exp_le_exp.2 ?_)
    apply mul_le_mul_of_nonneg_left _ hx0
    have : 2 * ((1 + η) / (p : ℝ)) ≤ c := by
      rw [hc, mul_div_assoc]; linarith
    linarith
  have hprod : ∏ p ∈ F, (1 - (1 + η) / (p : ℝ))⁻¹ ≤ exp (β * ∑ p ∈ F, (1 : ℝ) / p) := by
    calc ∏ p ∈ F, (1 - (1 + η) / (p : ℝ))⁻¹
        ≤ ∏ p ∈ F, exp ((1 + η) / (p : ℝ) * (1 + c)) := by
          apply prod_le_prod₀ _ hfac
          intro p hp
          simp only [hF, mem_filter] at hp
          have hpY : Y ≤ (p : ℝ) := le_trans hYu hp.2.2.1
          have : (1 + η) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
          exact inv_nonneg.2 (by linarith)
      _ = exp (β * ∑ p ∈ F, (1 : ℝ) / p) := by
          rw [← exp_sum, mul_sum]
          congr 1
          apply sum_congr rfl
          intro p _
          rw [hβ]; ring
  have hsum := hC u w (by linarith) huw
  have hexp : β * ∑ p ∈ F, (1 : ℝ) / p ≤ log R + (t / 4 + t / 4 + t / 2) := by
    have h1 : β * ∑ p ∈ F, (1 : ℝ) / p ≤ β * (log R + C / log u) :=
      mul_le_mul_of_nonneg_left hsum hβ0
    have hlogR0 : 0 ≤ log R := log_nonneg hR1.le
    -- (β - 1) log R ≤ η L + 2 c L
    have hb1 : β - 1 ≤ η + 2 * c := by rw [hβ]; nlinarith
    have hcL : 2 * c * L ≤ t / 4 := by
      have : c ≤ 3 / Y := by
        rw [hc]; apply div_le_div_of_nonneg_right _ (by linarith); linarith
      have hY0 : 0 < Y := by linarith
      have h24 : 24 * L ≤ Y * t := by
        have := hYL; rw [div_le_iff₀ ht0] at this; linarith
      calc 2 * c * L ≤ 2 * (3 / Y) * L := by gcongr
        _ = 6 * L / Y := by ring
        _ ≤ t / 4 := by rw [div_le_iff₀ hY0]; linarith
    have hpart1 : (β - 1) * log R ≤ t / 4 + t / 4 := by
      have hb0 : 0 ≤ β - 1 := by rw [hβ]; nlinarith
      calc (β - 1) * log R ≤ (η + 2 * c) * L := by
            apply mul_le_mul hb1 hlogR hlogR0 (by positivity)
        _ = η * L + 2 * c * L := by ring
        _ ≤ t / 4 + t / 4 := by linarith
    have hpart2 : β * (C / log u) ≤ t / 2 := by
      have hlogYu : log Y ≤ log u := log_le_log (by linarith) hYu
      have hlu : 6 * C / t + 1 ≤ log u := le_trans hlogY hlogYu
      have hCt : 6 * C ≤ t * (log u - 1) := by
        have h6 : 6 * C / t ≤ log u - 1 := by linarith
        rw [div_le_iff₀ ht0] at h6; linarith
      have : C / log u ≤ t / 6 := by
        rw [div_le_iff₀ hlogu]; nlinarith
      have hCu : 0 ≤ C / log u := div_nonneg hC0 hlogu.le
      calc β * (C / log u) ≤ 3 * (C / log u) := mul_le_mul_of_nonneg_right hβ3 hCu
        _ ≤ 3 * (t / 6) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = t / 2 := by ring
    have hexpand : β * (log R + C / log u) = log R + (β - 1) * log R + β * (C / log u) := by ring
    calc β * ∑ p ∈ F, (1 : ℝ) / p ≤ β * (log R + C / log u) := h1
      _ = log R + (β - 1) * log R + β * (C / log u) := hexpand
      _ ≤ log R + (t / 4 + t / 4) + t / 2 := add_le_add (add_le_add le_rfl hpart1) hpart2
      _ = log R + (t / 4 + t / 4 + t / 2) := by ring
  have hfin : exp (β * ∑ p ∈ F, (1 : ℝ) / p) ≤ (1 + ε) * R := by
    have hR0 : 0 < R := by linarith
    have e1 : exp t = 1 + ε := exp_log (by linarith)
    have e2 : exp (log R) = R := exp_log hR0
    have hle : β * ∑ p ∈ F, (1 : ℝ) / p ≤ log R + t := by
      have : t / 4 + t / 4 + t / 2 = t := by ring
      rw [this] at hexp; exact hexp
    calc exp (β * ∑ p ∈ F, (1 : ℝ) / p) ≤ exp (log R + t) := exp_le_exp.2 hle
      _ = R * (1 + ε) := by rw [exp_add, e1, e2]
      _ = (1 + ε) * R := mul_comm _ _
  exact le_trans hprod hfin

end LeanLab.BS2022GRH.SieveAllLevels1611

#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.mertens_sum_range
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.inv_one_sub_le_exp
#print axioms LeanLab.BS2022GRH.SieveAllLevels1611.mertens_range_product_split
