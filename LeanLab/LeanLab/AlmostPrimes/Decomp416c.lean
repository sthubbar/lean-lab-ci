import LeanLab.AlmostPrimes.Decomp416b

/-!
AI wrote the Lean code. Goldbach is open.
Campbell 2026 v1, https://arxiv.org/abs/2608.09488v1,
printed pages 10 and 11, the proof of Lemma 4.3.
This follows the printed exponential estimate with alpha equal to 0.3246.
The prime reciprocal estimate remains a cited input.
-/

open Real Finset

noncomputable section
namespace LeanLab.AlmostPrimes.Decomp416c
open CampbellCase2 CampbellLemma43 Decomp416a Decomp416b

/-- LEAF. Campbell pages 10 and 11, the exponential estimate after equation 4.4.
The reciprocal prime sum is an explicit hypothesis. The logarithm-weighted prime
sum is supplied by the existing unconditional RSLogSum theorem. -/
theorem rankin_exp_bound (z : ℝ) (hz : 1000 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) < z) (s α B : ℝ)
    (hα : 0 < α) (hαL : α < log z)
    (hrec : ∑ p ∈ P, (1 : ℝ) / p ≤ log (log z) + B) :
    ∑ t ∈ P.powerset.filter
        (fun t : Finset ℕ => (∏ p ∈ t, ((p : ℕ) : ℝ)) < z ^ s), (8 : ℝ) ^ t.card ≤
      z ^ s * log z ^ 8 * exp (8 * B + 8 * α * exp α - s * α) := by
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < log z := Real.log_pos (by linarith)
  let η := α / log z
  let δ := 1 - η
  have hη0 : 0 < η := div_pos hα hL0
  have hη1 : η < 1 := (div_lt_one hL0).mpr hαL
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  let w : ℕ → ℝ := fun p => 8 * (p : ℝ) ^ (-δ)
  have hp0 : ∀ p ∈ P, (0 : ℝ) < p := fun p hp => by exact_mod_cast (hP p hp).1.pos
  have hweighted := RSLogSum.sum_log_div_lt_log_real z hz P hP
  have hηL : η * log z = α := by dsimp [η]; field_simp
  have hw : ∑ p ∈ P, w p ≤
      8 * ∑ p ∈ P, (1 : ℝ) / p + 8 * η * exp α * ∑ p ∈ P, log p / p := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hp' := hp0 p hp
    have hlp : 0 ≤ log p := Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)
    have hlpz : log p ≤ log z := Real.log_le_log hp' (hP p hp).2.le
    have hx : η * log p ≤ α := by
      calc η * log p ≤ η * log z := mul_le_mul_of_nonneg_left hlpz hη0.le
        _ = α := hηL
    have he : exp (η * log p) ≤ 1 + η * log p * exp α := by
      have hb := DDLemma23.exp_le_one_add_mul_exp (η * log p)
      have hc := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx)
        (mul_nonneg hη0.le hlp)
      linarith
    have heq : (p : ℝ) ^ (-δ) = exp (η * log p) / p := by
      rw [Real.rpow_def_of_pos hp', show log p * -δ = η * log p - log p by dsimp [δ]; ring,
        Real.exp_sub, Real.exp_log hp']
    dsimp only [w]
    rw [heq]
    have hdiv := div_le_div_of_nonneg_right he hp'.le
    nlinarith [show (1 + η * log p * exp α) / p = 1 / p + η * exp α * (log p / p) by ring]
  have hexp : ∑ p ∈ P, w p ≤ 8 * log (log z) + 8 * B + 8 * α * exp α := by
    have h1 := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul_of_nonneg_left hweighted.le
      (by positivity : 0 ≤ 8 * η * exp α)
    have he : 8 * η * exp α * log z = 8 * α * exp α := by rw [← hηL]; ring
    rw [he] at h2
    linarith
  have hDδ : (z ^ s) ^ δ = z ^ s * exp (-(s * α)) := by
    rw [← Real.rpow_mul hz0.le, Real.rpow_def_of_pos hz0, Real.rpow_def_of_pos hz0,
      ← Real.exp_add]
    congr 1
    dsimp [δ, η]
    field_simp
    ring
  have hL8 : exp (8 * log (log z)) = log z ^ 8 := by
    rw [show (8 : ℝ) * log (log z) = ((8 : ℕ) : ℝ) * log (log z) by norm_num,
      ← Real.log_pow, Real.exp_log (by positivity)]
  calc _ ≤ (z ^ s) ^ δ * ∏ p ∈ P, (1 + 8 / (p : ℝ) ^ δ) :=
      rankin_divisor_sum P (fun p hp => (hP p hp).1) (z ^ s) δ (by positivity) hδ
    _ = (z ^ s) ^ δ * ∏ p ∈ P, (1 + w p) := by
      congr 1
      apply prod_congr rfl
      intro p hp
      dsimp [w]
      rw [Real.rpow_neg (hp0 p hp).le, div_eq_mul_inv]
    _ ≤ (z ^ s) ^ δ * exp (∑ p ∈ P, w p) :=
      mul_le_mul_of_nonneg_left (Real.prod_one_add_le_exp_sum P (fun p => by dsimp [w]; positivity))
        (by positivity)
    _ ≤ (z ^ s) ^ δ * exp (8 * log (log z) + 8 * B + 8 * α * exp α) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by
      rw [hDδ, ← hL8]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Campbell page 11, Lemma 4.3 with the printed constant and exponent.
CONDITIONAL ON the prime reciprocal bound used in the printed proof. -/
theorem lemma43_of_reciprocal_sum (N : ℕ) (hN : 2 ≤ N) (z : ℝ)
    (hz : (10 : ℝ) ^ 8 ≤ z)
    (hrec : ∑ p ∈ primesBelow z, (1 : ℝ) / p ≤ log (log z) + 0.263 - 1 / 3) :
    R4A N z (z ^ (14.66 : ℝ)) < 0.563 * z ^ (14.66 : ℝ) * log z ^ 8 := by
  have hz0 : 0 < z := by linarith
  have hL : (0.3246 : ℝ) < log z := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 8) hz
    rw [Real.log_pow] at hlog
    have hten := RS1962.log_ten_gt
    norm_num at hlog
    linarith
  have hP : ∀ p ∈ primesBelow z, p.Prime ∧ (p : ℝ) < z := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := mem_primesBelow.mp hp
    exact ⟨h1, h3⟩
  have hb := rankin_exp_bound z (by linarith) (primesBelow z) hP
    14.66 0.3246 (0.263 - 1 / 3) (by norm_num) hL (by linarith)
  calc R4A N z (z ^ (14.66 : ℝ)) ≤ (19 / 6 : ℝ) *
        ∑ t ∈ (primesBelow z).powerset.filter
          (fun t : Finset ℕ => (∏ p ∈ t, ((p : ℕ) : ℝ)) < z ^ (14.66 : ℝ)), (8 : ℝ) ^ t.card :=
      R4A_le_divisor_sum N hN z _
    _ ≤ (19 / 6 : ℝ) * (z ^ (14.66 : ℝ) * log z ^ 8 *
        exp (8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = z ^ (14.66 : ℝ) * log z ^ 8 * ((19 / 6 : ℝ) *
        exp (8 * (0.263 - 1 / 3) + 8 * 0.3246 * exp 0.3246 - 14.66 * 0.3246)) := by ring
    _ < z ^ (14.66 : ℝ) * log z ^ 8 * 0.563 :=
      mul_lt_mul_of_pos_left Campbell43.lemma4_3_const (by
        have : 0 < log z := by linarith
        positivity)
    _ = _ := by ring

/-- Campbell page 11, the reciprocal estimate with the prime three removed,
from Rosser and Schoenfeld page 70, Theorem 5, equation 3.18.
CONDITIONAL ON that explicit prime sum bound. -/
theorem reciprocal_sum_of_RS318 {B : ℝ} (hB : B < 0.2614973)
    (hRS : RS1962.RS318 B) (z : ℝ) (hz : (10 : ℝ) ^ 8 ≤ z) :
    ∑ p ∈ primesBelow z, (1 : ℝ) / p ≤ log (log z) + 0.263 - 1 / 3 := by
  have hL : (18.4192 : ℝ) < log z := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 8) hz
    rw [Real.log_pow] at hlog
    have hten := RS1962.log_ten_gt
    norm_num at hlog
    linarith
  have hL0 : 0 < log z := by linarith
  have herror : 1 / (2 * log z ^ 2) < (0.0015 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * log z ^ 2)).mpr
    nlinarith
  have h3 : 3 ∉ primesBelow z := by
    intro h
    exact (mem_primesBelow.mp h).2.1 rfl
  have hsub : insert 3 (primesBelow z) ⊆ (range (⌊z⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · simp only [mem_filter, mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor (by linarith : (3 : ℝ) ≤ z)), Nat.prime_three⟩
    · obtain ⟨hpp, _, hpz⟩ := mem_primesBelow.mp hp
      simp only [mem_filter, mem_range]
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpz.le), hpp⟩
  have hsum : (∑ p ∈ primesBelow z, (1 : ℝ) / p) + 1 / 3 ≤ RS1962.primeRecipSum z := by
    calc
      _ = ∑ p ∈ insert 3 (primesBelow z), (1 : ℝ) / p := by
        rw [sum_insert h3]
        norm_num
        ring
      _ ≤ RS1962.primeRecipSum z :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hbound := hRS z (by linarith)
  linarith

/-- Campbell page 11, Lemma 4.3, with its written proof and original parameter alpha.
CONDITIONAL ON Rosser and Schoenfeld equation 3.18. -/
theorem lemma43_of_RS318 {B : ℝ} (hB : B < 0.2614973) (hRS : RS1962.RS318 B) :
    CampbellCase3X.Lemma43 R4paper := by
  intro N hN
  have hN2 : 2 ≤ N := by
    have : 2 ≤ CampbellCase3.N1 := by unfold CampbellCase3.N1; norm_num
    exact this.trans hN
  exact (lemma43_of_reciprocal_sum N hN2 (CampbellCase2.zOf N)
    (CampbellCase3X.z_ge_1e8 hN)
    (reciprocal_sum_of_RS318 hB hRS _ (CampbellCase3X.z_ge_1e8 hN))).le

example : (1000 : ℝ) ≤ 1000 ∧ (0 : ℝ) < 1 ∧ 1 < log 1000 ∧
    (∑ p ∈ (∅ : Finset ℕ), (1 : ℝ) / p) ≤ log (log 1000) + 0 := by
  have hL : (1 : ℝ) < log 1000 := by
    have hten := RS1962.log_ten_gt
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith
  refine ⟨le_rfl, by norm_num, hL, ?_⟩
  simpa using Real.log_nonneg hL.le

end LeanLab.AlmostPrimes.Decomp416c

#print axioms LeanLab.AlmostPrimes.Decomp416c.rankin_exp_bound
#print axioms LeanLab.AlmostPrimes.Decomp416c.lemma43_of_reciprocal_sum
#print axioms LeanLab.AlmostPrimes.Decomp416c.reciprocal_sum_of_RS318
#print axioms LeanLab.AlmostPrimes.Decomp416c.lemma43_of_RS318
