/-
P0076, Section 4, Proposition 4.2, pages 13 to 14.
Split of paper_enveloping_level_set_input by the size of delta against a power of M,
following Green and Tao, Restriction theory of the Selberg sieve, Section 4, arXiv math/0405581.
Small delta: Parseval plus the growth bound, proved here. Large delta: a cited LEAF.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.EnvelopingRestrictionSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Green Tao Section 4, Parseval on Z_N: additivity of the additive character. -/
theorem lss_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Green Tao Section 4, Parseval on Z_N: natural multiples in the additive character. -/
theorem lss_eC_nat_mul (k : ℕ) (x : ℝ) : eC ((k : ℝ) * x) = (eC x) ^ k := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Green Tao Section 4, Parseval on Z_N: the additive character is 1 at integers. -/
theorem lss_eC_int (m : ℤ) : eC ((m : ℝ)) = 1 := by
  rw [show eC ((m : ℝ)) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) from rfl]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) =
    (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- Green Tao Section 4, Parseval on Z_N: the additive character is 1 only at integers. -/
theorem lss_eC_eq_one {y : ℝ} (h : eC y = 1) : ∃ m : ℤ, y = m := by
  unfold eC at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have : ((y : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ h2
    rw [hn]
    ring
  exact_mod_cast this

/-- Green Tao Section 4, Parseval on Z_N: orthogonality of the additive characters mod P. -/
theorem lss_orth (P : ℕ) (hP : P ≠ 0) (x : ℤ) :
    ∑ k ∈ range P, eC ((k : ℝ) * x / P) = if (P : ℤ) ∣ x then (P : ℂ) else 0 := by
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP
  have hterm : ∀ k : ℕ, eC ((k : ℝ) * x / P) = eC ((x : ℝ) / P) ^ k := by
    intro k
    rw [← lss_eC_nat_mul]
    congr 1
    ring
  rw [sum_congr rfl (fun k _ => hterm k)]
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    have h1 : eC ((x : ℝ) / P) = 1 := by
      rw [hm]
      push_cast
      rw [show ((P : ℝ) * m / P) = (m : ℝ) by field_simp]
      exact lss_eC_int m
    simp [h1]
  · have hne : eC ((x : ℝ) / P) ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := lss_eC_eq_one h1
      apply h
      refine ⟨m, ?_⟩
      have : (x : ℝ) = (P : ℝ) * m := by
        rw [div_eq_iff hPr] at hm
        rw [hm]
        ring
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have h2 : eC ((x : ℝ) / P) ^ P = 1 := by
      rw [← lss_eC_nat_mul, show (P : ℝ) * ((x : ℝ) / P) = (x : ℝ) by field_simp]
      exact lss_eC_int x
    rw [h2, sub_self, zero_div]

/-- Green Tao Section 4, Parseval on Z_N: conjugation of the additive character. -/
theorem lss_eC_conj (x : ℝ) : (starRingEnd ℂ) (eC x) = eC (-x) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- Green Tao Section 4, Parseval on Z_N: two representatives below M agree when M divides their difference. -/
theorem lss_dvd_iff {M n m : ℕ} (hn : n < M) (hm : m < M) :
    (M : ℤ) ∣ ((m : ℤ) - n) ↔ n = m := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    have h1 : k = 0 := by
      by_contra hk0
      rcases lt_or_gt_of_ne hk0 with hk' | hk'
      · have : (M : ℤ) * k ≤ -M := by nlinarith
        omega
      · have : (M : ℤ) ≤ (M : ℤ) * k := by nlinarith
        omega
    subst h1
    omega
  · rintro rfl
    simp

/-- Parseval's identity for the normalized transform complexFhat on representatives 0 through M minus 1,
as used in Green Tao, proof of Proposition 4.1, page 155. -/
theorem parseval_complexFhat (M : ℕ) (hM : M ≠ 0) (g : ℕ → ℂ) :
    ∑ ξ ∈ range M, ‖complexFhat M g ξ‖ ^ 2 = (M : ℝ)⁻¹ * ∑ n ∈ range M, ‖g n‖ ^ 2 := by
  apply Complex.ofReal_injective
  have hsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast [Complex.ofReal_sum]
  simp only [← Complex.ofReal_pow, hsq]
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hexp : ∀ ξ ∈ range M, complexFhat M g ξ * (starRingEnd ℂ) (complexFhat M g ξ) =
      (M : ℂ)⁻¹ * (M : ℂ)⁻¹ * ∑ n ∈ range M, ∑ m ∈ range M,
        g n * (starRingEnd ℂ) (g m) * eC ((ξ : ℝ) * (((m : ℤ) - n : ℤ) : ℝ) / M) := by
    intro ξ _
    unfold complexFhat
    simp only [map_mul, map_inv₀, map_natCast, map_sum, lss_eC_conj, neg_neg]
    rw [mul_mul_mul_comm, sum_mul_sum]
    congr 1
    apply sum_congr rfl; intro n _; apply sum_congr rfl; intro m _
    rw [show g n * (starRingEnd ℂ) (g m) * eC ((ξ : ℝ) * (((m : ℤ) - n : ℤ) : ℝ) / M) =
      g n * (starRingEnd ℂ) (g m) * (eC (-((ξ : ℝ) * n / M)) * eC ((ξ : ℝ) * m / M)) by
        rw [← lss_eC_add]; congr 2; push_cast; ring]
    ring
  rw [sum_congr rfl hexp, ← mul_sum, sum_comm]
  have hinner : ∀ n ∈ range M, ∑ ξ ∈ range M, ∑ m ∈ range M,
      g n * (starRingEnd ℂ) (g m) * eC ((ξ : ℝ) * (((m : ℤ) - n : ℤ) : ℝ) / M) =
      (M : ℂ) * (g n * (starRingEnd ℂ) (g n)) := by
    intro n hn
    rw [sum_comm]
    have hm : ∀ m ∈ range M, ∑ ξ ∈ range M,
        g n * (starRingEnd ℂ) (g m) * eC ((ξ : ℝ) * (((m : ℤ) - n : ℤ) : ℝ) / M) =
        if n = m then (M : ℂ) * (g n * (starRingEnd ℂ) (g n)) else 0 := by
      intro m hm'
      rw [← mul_sum, lss_orth M hM]
      have hiff := lss_dvd_iff (mem_range.mp hn) (mem_range.mp hm')
      by_cases h : n = m
      · subst h
        rw [if_pos (hiff.mpr rfl), if_pos rfl]; ring
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
    rw [sum_congr rfl hm, sum_ite_eq]
    simp [hn]
  rw [sum_congr rfl hinner, ← mul_sum]
  field_simp

/-- Green Tao, proof of Proposition 4.1, page 155: Parseval with a crude pointwise bound B on the
weight gives the level set count times delta squared at most B. -/
theorem level_set_of_sup (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n) {B : ℝ}
    (hB : ∀ n < M, β n ≤ B) (a : ℕ → ℂ) (δ : ℝ) (hδ : 0 < δ) :
    (((range M).filter (fun ξ =>
      δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ ^ 2 * β n) ^ ((1 : ℝ) / 2) <
      ‖complexFhat M (fun n => a n * (β n : ℂ)) ξ‖)).card : ℝ) * δ ^ 2 ≤ B := by
  set S : ℝ := (M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ ^ 2 * β n with hSdef
  set F : ℕ → ℝ := fun ξ => ‖complexFhat M (fun n => a n * (β n : ℂ)) ξ‖ with hF
  have hM0 : M ≠ 0 := by omega
  have hB0 : 0 ≤ B := (hβ0 0).trans (hB 0 (by omega))
  have hS : 0 ≤ S := mul_nonneg (by positivity)
    (sum_nonneg (fun n _ => mul_nonneg (by positivity) (hβ0 n)))
  have hE2 : (S ^ ((1 : ℝ) / 2)) ^ 2 = S := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]; norm_num
  have hpars : ∑ ξ ∈ range M, F ξ ^ 2 ≤ B * S := by
    simp only [hF]
    rw [parseval_complexFhat M hM0, hSdef, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 n)]
    have := hB n (mem_range.mp hn)
    have h2 : 0 ≤ ‖a n‖ ^ 2 * β n := mul_nonneg (by positivity) (hβ0 n)
    nlinarith
  set T := (range M).filter (fun ξ => δ * S ^ ((1 : ℝ) / 2) < F ξ) with hT
  have hlow : (T.card : ℝ) * (δ ^ 2 * S) ≤ ∑ ξ ∈ range M, F ξ ^ 2 := by
    calc (T.card : ℝ) * (δ ^ 2 * S) = ∑ ξ ∈ T, (δ * S ^ ((1 : ℝ) / 2)) ^ 2 := by
          rw [sum_const, nsmul_eq_mul, mul_pow, hE2]
      _ ≤ ∑ ξ ∈ T, F ξ ^ 2 := by
          apply sum_le_sum
          intro ξ hξ
          have h1 := (mem_filter.mp hξ).2
          have h0 : 0 ≤ δ * S ^ ((1 : ℝ) / 2) := mul_nonneg hδ.le (Real.rpow_nonneg hS _)
          exact pow_le_pow_left₀ h0 h1.le 2
      _ ≤ ∑ ξ ∈ range M, F ξ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  show (T.card : ℝ) * δ ^ 2 ≤ B
  rcases hS.eq_or_lt with h0 | hSpos
  · have hempty : T = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro ξ hξ hlt
      rw [← h0, Real.zero_rpow (by norm_num), mul_zero] at hlt
      have hsum : ∑ ξ ∈ range M, F ξ ^ 2 ≤ 0 := by rw [← h0, mul_zero] at hpars; exact hpars
      have hle : F ξ ^ 2 ≤ ∑ ξ ∈ range M, F ξ ^ 2 :=
        single_le_sum (f := fun ξ => F ξ ^ 2) (fun _ _ => sq_nonneg _) hξ
      nlinarith
    rw [hempty, card_empty, Nat.cast_zero, zero_mul]
    exact hB0
  · have := hlow.trans hpars
    have h' : (T.card : ℝ) * δ ^ 2 * S ≤ B * S := by linarith
    exact le_of_mul_le_mul_right h' hSpos

/-- Small delta regime of the level set estimate, delta at most M to the power minus c.
Green Tao, proof of Proposition 4.1, page 155, crude bound plus Parseval: with the growth half of
EnvelopingFourierBounds at exponent epsilon times c the count is at most A of epsilon c times
M to the power epsilon c over delta squared, and M to the power epsilon c is at most delta to the
power minus epsilon. -/
theorem level_set_small_delta (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c →
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ → δ ≤ (M : ℝ) ^ (-c) →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ A (ε * c) * δ ^ (-(2 + ε)) := by
  intro ε hε c hc J w _ _ b _ _ _ M hM hB a δ hδ hδM
  have hεc : 0 < ε * c := mul_pos hε hc
  have hMp : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hcard := level_set_of_sup M hM (restrictionBeta w (WW J w) b M)
    (restrictionBeta_nonneg w (WW J w) b M) (hB.1 (ε * c) hεc) a δ hδ
  have hMc : (M : ℝ) ^ c ≤ δ⁻¹ := by
    rw [Real.rpow_neg hMp.le] at hδM
    exact (le_inv_comm₀ hδ (Real.rpow_pos_of_pos hMp c)).mp hδM
  have hpow : (M : ℝ) ^ (ε * c) ≤ δ ^ (-ε) := by
    rw [mul_comm, Real.rpow_mul hMp.le, Real.rpow_neg hδ.le, ← Real.inv_rpow hδ.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hMp.le _) hMc hε.le
  have hA := (hAD (ε * c) hεc).1
  have hd2 : 0 < δ ^ 2 := by positivity
  have hsplit : δ ^ (-(2 + ε)) = δ ^ (-ε) * (δ ^ 2)⁻¹ := by
    rw [show -(2 + ε) = -ε + -2 by ring, Real.rpow_add hδ, Real.rpow_neg hδ.le (2 : ℝ),
      Real.rpow_two]
  rw [hsplit, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hd2]
  exact hcard.trans (mul_le_mul_of_nonneg_left hpow hA.le)

/-- LEAF: Green and Tao, Restriction theory of the Selberg sieve, arXiv math/0405581, proof of
Proposition 4.1 pages 155 to 158 and its dual Proposition 4.2, the small spectrum case handled
with the rational Fourier expansion display 3.3. Class HARD. Level set form used by P0076 pages
13 to 14: for each epsilon some c and K, uniform under EnvelopingFourierBounds, bound by
K delta^(-2-epsilon) the frequencies where the transform of a times the capped weight exceeds
delta times the weighted L2 norm of a, for delta above M^(-c). -/
theorem paper_level_set_large_delta (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ → (M : ℝ) ^ (-c) < δ →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ K * δ ^ (-(2 + ε)) := by
  sorry

/-- Proposition 4.2, pages 13 to 14, the level set estimate assembled from the proved small delta
regime and the large delta LEAF. Exactly the statement of paper_enveloping_level_set_input.
CONDITIONAL ON paper_level_set_large_delta. -/
theorem paper_enveloping_level_set_input_of_leaves (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ K * δ ^ (-(2 + ε)) := by
  intro ε hε
  obtain ⟨c, hc, K1, hK1, H⟩ := paper_level_set_large_delta A D hAD ε hε
  have hA := (hAD (ε * c) (mul_pos hε hc)).1
  refine ⟨K1 + A (ε * c), by linarith, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM hB a δ hδ
  have hpow : 0 ≤ δ ^ (-(2 + ε)) := Real.rpow_nonneg hδ.le _
  rcases le_or_gt δ ((M : ℝ) ^ (-c)) with hsmall | hlarge
  · refine (level_set_small_delta A D hAD ε hε c hc J w hJ hw b hb hbW hamen M hM hB a δ hδ
      hsmall).trans ?_
    nlinarith
  · refine (H J w hJ hw b hb hbW hamen M hM hB a δ hδ hlarge).trans ?_
    nlinarith

end LeanLab.Teravainen2016
