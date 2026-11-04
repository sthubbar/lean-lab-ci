/-
Cai 2002 page 604 equation 4.15. The all large prime pair region.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Coefficient118
open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- Ordered prime pairs have unique products. Derived check for page 604 equation 4.15. -/
theorem ordered_prime_product_unique306 (p q r t : ℕ)
    (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime) (ht : t.Prime)
    (hpq : p < q) (hrt : r < t) (heq : p * q = r * t) : p = r ∧ q = t := by
  have hdiv : p ∣ r * t := by rw [← heq]; exact dvd_mul_right p q
  rcases hp.dvd_mul.mp hdiv with hpr | hpt
  · have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    subst r
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos heq⟩
  · have hpt' : p = t := (Nat.prime_dvd_prime_iff_eq hp ht).mp hpt
    subst t
    have hqr : q = r := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa only [mul_comm] using heq
    omega

/-- The all large pair region of equation 4.15, with coprimality inherited from S3. -/
def switchedThreePairs306 (N : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter (fun b =>
    b.1.Prime ∧ b.2.Prime ∧ z2 N ≤ (b.1 : ℝ) ∧ b.1 < b.2 ∧
      (b.2 : ℝ) < ((N : ℝ) / (b.1 : ℝ)) ^ (1 / 2 : ℝ) ∧
        Nat.Coprime (b.1 * b.2) N)

/-- The finite enumeration is exactly the all large prime pair region.
Page 604 equation 4.15. -/
theorem mem_switchedThreePairs306 (N p q : ℕ) (hN : 2 ≤ N) :
    (p, q) ∈ switchedThreePairs306 N ↔
      p.Prime ∧ q.Prime ∧ z2 N ≤ (p : ℝ) ∧ p < q ∧
        (q : ℝ) < ((N : ℝ) / (p : ℝ)) ^ (1 / 2 : ℝ) ∧ Nat.Coprime (p * q) N := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    obtain ⟨hp, hq, hpz, hpq, hqroot, hc⟩ := h
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hroot : (((N : ℝ) / p) ^ (1 / 2 : ℝ)) ^ 2 = (N : ℝ) / p := by
      rw [← rpow_natCast, ← rpow_mul (div_nonneg hNr.le hpr.le)]
      norm_num
    have hqsq : (q : ℝ) ^ 2 < (N : ℝ) / p := by
      rw [← hroot]
      nlinarith [rpow_pos_of_pos (div_pos hNr hpr) (1 / 2 : ℝ)]
    have hprodR : (p : ℝ) * (q : ℝ) ^ 2 < N := by
      have hh := (lt_div_iff₀ hpr).mp hqsq
      nlinarith only [hh]
    have hprod : p * q ^ 2 < N := by exact_mod_cast hprodR
    have hpositive : 0 < p * q ^ 2 := Nat.mul_pos hp.pos (pow_pos hq.pos _)
    have hp_le : p ≤ p * q ^ 2 := Nat.le_of_dvd hpositive (dvd_mul_right p (q ^ 2))
    have hqdiv : q ∣ p * q ^ 2 := by
      refine ⟨p * q, ?_⟩
      ring
    have hq_le : q ≤ p * q ^ 2 := Nat.le_of_dvd hpositive hqdiv
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, hp, hq, hpz, hpq, hqroot, hc⟩

/-- The product support in the all large region of equation 4.15. -/
def switchedThreeE306 (N : ℕ) : Finset ℕ :=
  (switchedThreePairs306 N).image (fun b => b.1 * b.2)

/-- The representation coefficient for the all large region of equation 4.15. -/
def switchedThreeMultiplicity306 (N a : ℕ) : ℕ :=
  pairMultiplicity118 (switchedThreePairs306 N) a

/-- The all large coefficient is at most one by the order of the two primes.
Page 604 equation 4.15. -/
theorem switchedThreeMultiplicity_le_one306 (N a : ℕ) :
    switchedThreeMultiplicity306 N a ≤ 1 := by
  unfold switchedThreeMultiplicity306 pairMultiplicity118
  apply card_le_one.mpr
  intro b hb c hc
  obtain ⟨hbT, hba⟩ := mem_filter.mp hb
  obtain ⟨hcT, hca⟩ := mem_filter.mp hc
  obtain ⟨hb1, hb2, _, hb12, _, _⟩ := (mem_filter.mp hbT).2
  obtain ⟨hc1, hc2, _, hc12, _, _⟩ := (mem_filter.mp hcT).2
  have heq := ordered_prime_product_unique306 b.1 b.2 c.1 c.2
    hb1 hb2 hc1 hc2 hb12 hc12 (hba.trans hca.symm)
  exact Prod.ext heq.1 heq.2

/-- The coefficient is exactly the indicator of the all large product support.
Page 604 equation 4.15. -/
theorem switchedThreeMultiplicity_indicator306 (N a : ℕ) :
    switchedThreeMultiplicity306 N a = if a ∈ switchedThreeE306 N then 1 else 0 := by
  have hpos : 0 < switchedThreeMultiplicity306 N a ↔ a ∈ switchedThreeE306 N := by
    constructor
    · intro h
      obtain ⟨b, hb⟩ := card_pos.mp h
      obtain ⟨hbT, hba⟩ := mem_filter.mp hb
      exact mem_image.mpr ⟨b, hbT, hba⟩
    · intro h
      obtain ⟨b, hbT, hba⟩ := mem_image.mp h
      exact card_pos.mpr ⟨b, mem_filter.mpr ⟨hbT, hba⟩⟩
  have hle := switchedThreeMultiplicity_le_one306 N a
  split_ifs with ha
  · have := hpos.mpr ha
    omega
  · have := mt hpos.mp ha
    omega

/-- The square sum condition is uniform in N for the all large coefficient.
Cai page 599 Lemma 4 and page 604 equation 4.15. -/
theorem switchedThreeMultiplicity_log_bound306 (N : ℕ) (x : ℝ) (hx : exp 1 ≤ x) :
    ∑ a ∈ Icc 1 ⌊x⌋₊, (switchedThreeMultiplicity306 N a : ℝ) ^ 2 / (a : ℝ) ≤ 2 * log x := by
  have hx1 : 1 ≤ x := (one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans hx
  have hlog : 1 ≤ log x := by simpa using log_le_log (exp_pos 1) hx
  have hs : ∑ a ∈ Icc 1 ⌊x⌋₊, (switchedThreeMultiplicity306 N a : ℝ) ^ 2 / (a : ℝ) ≤
      (harmonic ⌊x⌋₊ : ℝ) := by
    calc
      _ ≤ ∑ a ∈ Icc 1 ⌊x⌋₊, (a : ℝ)⁻¹ := by
        apply sum_le_sum
        intro a _
        rw [← one_div]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg a)
        have hg : (switchedThreeMultiplicity306 N a : ℝ) ≤ 1 := by
          exact_mod_cast switchedThreeMultiplicity_le_one306 N a
        have hg0 := Nat.cast_nonneg (α := ℝ) (switchedThreeMultiplicity306 N a)
        nlinarith
      _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact hs.trans ((harmonic_floor_le_one_add_log x hx1).trans (by linarith))

example : Nat.Prime 17 ∧ Nat.Prime 19 ∧ z2 8192 ≤ 17 ∧ 17 < (19 : ℕ) ∧
    (19 : ℝ) < ((8192 : ℝ) / 17) ^ (1 / 2 : ℝ) ∧ Nat.Coprime (17 * 19) 8192 := by
  have hz : z2 8192 ≤ 17 := by
    have he : (8192 : ℝ) ^ (4 / 13 : ℝ) = 16 := by
      rw [show (8192 : ℝ) = (2 : ℝ) ^ (13 : ℝ) by norm_num,
        ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    apply le_trans (rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8192)
      (by norm_num : (1 / 3.29 : ℝ) ≤ 4 / 13))
    rw [he]
    norm_num
  refine ⟨by norm_num, by norm_num, hz, by norm_num, ?_, by norm_num⟩
  rw [← sqrt_eq_rpow]
  exact Real.lt_sqrt_of_sq_lt (by norm_num)

#print axioms mem_switchedThreePairs306
#print axioms ordered_prime_product_unique306
#print axioms switchedThreeMultiplicity_le_one306
#print axioms switchedThreeMultiplicity_indicator306
#print axioms switchedThreeMultiplicity_log_bound306
end LeanLab.Cai2002
