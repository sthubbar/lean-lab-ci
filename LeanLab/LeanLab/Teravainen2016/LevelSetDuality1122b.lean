/-
P0076, Proposition 4.2, pages 13 to 14: the duality step and the final arithmetic that turn
Green and Tao display 4.2, arXiv math/0405581 page 9, into the large delta level set count
paper_level_set_large_delta. Phases on the large spectrum, Cauchy Schwarz in L2 of the weight,
and the exponent bookkeeping delta^2 N^2 at most K N^(1+eps') giving N at most
K' delta^(-2-eps). burst-20261122 S69. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.LevelSetLarge1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.LevelSet1122b

open LeanLab.Teravainen2016

/-- The duality step, TT* in Cauchy Schwarz form: Green and Tao page 12, the duality argument
behind Proposition 4.2. If every frequency in Xi carries a transform of a times beta above
delta times the weighted L2 norm of a, then with the unimodular phases of those transforms,
(|Xi| delta)^2 is at most the weighted L2 mass of the dual exponential sum over Xi. -/
theorem level_set_duality (M : ℕ) (hM : 1 ≤ M) (β : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (a : ℕ → ℂ) (δ : ℝ) (hδ : 0 < δ) (Ξ : Finset ℕ)
    (hΞ : ∀ ξ ∈ Ξ, δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ ^ 2 * β n) ^ ((1 : ℝ) / 2) <
      ‖complexFhat M (fun n => a n * (β n : ℂ)) ξ‖) :
    ∃ f : ℕ → ℂ, (∀ x, ‖f x‖ ≤ 1) ∧
      ((Ξ.card : ℝ) * δ) ^ 2 ≤ (M : ℝ)⁻¹ * ∑ n ∈ range M, β n *
        ‖∑ x ∈ Ξ, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set F : ℕ → ℂ := fun ξ => complexFhat M (fun n => a n * (β n : ℂ)) ξ with hFdef
  set f : ℕ → ℂ := fun ξ => (starRingEnd ℂ) (F ξ) / (‖F ξ‖ : ℂ) with hfdef
  refine ⟨f, ?_, ?_⟩
  · intro x
    simp only [hfdef]
    by_cases h : F x = 0
    · simp [h]
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h)]
  set S : ℝ := (M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ ^ 2 * β n with hSdef
  set G : ℕ → ℂ := fun n => ∑ x ∈ Ξ, f x * eC (-((x : ℝ) * n / M)) with hGdef
  set T : ℝ := (M : ℝ)⁻¹ * ∑ n ∈ range M, β n * ‖G n‖ ^ 2 with hTdef
  show ((Ξ.card : ℝ) * δ) ^ 2 ≤ T
  have hS : 0 ≤ S := mul_nonneg (by positivity)
    (sum_nonneg (fun n _ => mul_nonneg (by positivity) (hβ0 n)))
  have hT : 0 ≤ T := mul_nonneg (by positivity)
    (sum_nonneg (fun n _ => mul_nonneg (hβ0 n) (by positivity)))
  have hfF : ∀ ξ, f ξ * F ξ = ((‖F ξ‖ : ℝ) : ℂ) := by
    intro ξ
    simp only [hfdef]
    by_cases h : F ξ = 0
    · simp [h]
    · have hn : ((‖F ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) (F ξ)), Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      field_simp
      push_cast
      ring
  -- the sum of the transforms with phases is the pairing of a beta with the dual sum G
  have hpair : ∑ ξ ∈ Ξ, f ξ * F ξ =
      (M : ℂ)⁻¹ * ∑ n ∈ range M, a n * (β n : ℂ) * G n := by
    simp only [hFdef, complexFhat, hGdef, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl; intro n _; apply sum_congr rfl; intro ξ _
    ring
  have hsumF : ∑ ξ ∈ Ξ, ‖F ξ‖ = ‖∑ ξ ∈ Ξ, f ξ * F ξ‖ := by
    simp only [hfF]
    rw [← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
  -- Cauchy Schwarz in L2 of beta
  have hCS : (∑ n ∈ range M, ‖a n‖ * β n * ‖G n‖) ^ 2 ≤
      (∑ n ∈ range M, ‖a n‖ ^ 2 * β n) * ∑ n ∈ range M, β n * ‖G n‖ ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (range M) (fun n => ‖a n‖ * Real.sqrt (β n))
      (fun n => Real.sqrt (β n) * ‖G n‖)
    have e1 : ∀ n, ‖a n‖ * Real.sqrt (β n) * (Real.sqrt (β n) * ‖G n‖) = ‖a n‖ * β n * ‖G n‖ := by
      intro n
      have := Real.mul_self_sqrt (hβ0 n)
      calc _ = ‖a n‖ * (Real.sqrt (β n) * Real.sqrt (β n)) * ‖G n‖ := by ring
        _ = _ := by rw [this]
    have e2 : ∀ n, (‖a n‖ * Real.sqrt (β n)) ^ 2 = ‖a n‖ ^ 2 * β n := by
      intro n; rw [mul_pow, Real.sq_sqrt (hβ0 n)]
    have e3 : ∀ n, (Real.sqrt (β n) * ‖G n‖) ^ 2 = β n * ‖G n‖ ^ 2 := by
      intro n; rw [mul_pow, Real.sq_sqrt (hβ0 n)]
    simp only [e1, e2, e3] at h
    exact h
  have hnorm : ‖(M : ℂ)⁻¹ * ∑ n ∈ range M, a n * (β n : ℂ) * G n‖ ≤
      (M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ * β n * ‖G n‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply sum_congr rfl; intro n _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hβ0 n)]
  have hP0 : 0 ≤ ∑ n ∈ range M, ‖a n‖ * β n * ‖G n‖ :=
    sum_nonneg (fun n _ => mul_nonneg (mul_nonneg (norm_nonneg _) (hβ0 n)) (norm_nonneg _))
  -- (sum of |F|)^2 at most S T
  have hmain : (∑ ξ ∈ Ξ, ‖F ξ‖) ^ 2 ≤ S * T := by
    rw [hsumF, hpair]
    have h1 := hnorm
    have h0 : 0 ≤ ‖(M : ℂ)⁻¹ * ∑ n ∈ range M, a n * (β n : ℂ) * G n‖ := norm_nonneg _
    calc ‖(M : ℂ)⁻¹ * ∑ n ∈ range M, a n * (β n : ℂ) * G n‖ ^ 2
        ≤ ((M : ℝ)⁻¹ * ∑ n ∈ range M, ‖a n‖ * β n * ‖G n‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (M : ℝ)⁻¹ ^ 2 * (∑ n ∈ range M, ‖a n‖ * β n * ‖G n‖) ^ 2 := by ring
      _ ≤ (M : ℝ)⁻¹ ^ 2 * ((∑ n ∈ range M, ‖a n‖ ^ 2 * β n) *
            ∑ n ∈ range M, β n * ‖G n‖ ^ 2) := mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = S * T := by rw [hSdef, hTdef]; ring
  have hE2 : (S ^ ((1 : ℝ) / 2)) ^ 2 = S := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]; norm_num
  have hlow : (Ξ.card : ℝ) * (δ * S ^ ((1 : ℝ) / 2)) ≤ ∑ ξ ∈ Ξ, ‖F ξ‖ := by
    calc (Ξ.card : ℝ) * (δ * S ^ ((1 : ℝ) / 2)) = ∑ ξ ∈ Ξ, δ * S ^ ((1 : ℝ) / 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ ξ ∈ Ξ, ‖F ξ‖ := sum_le_sum (fun ξ hξ => (hΞ ξ hξ).le)
  have hl0 : 0 ≤ (Ξ.card : ℝ) * (δ * S ^ ((1 : ℝ) / 2)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hδ.le (Real.rpow_nonneg hS _))
  have hsq : ((Ξ.card : ℝ) * δ) ^ 2 * S ≤ S * T := by
    have := (pow_le_pow_left₀ hl0 hlow 2).trans hmain
    calc ((Ξ.card : ℝ) * δ) ^ 2 * S = ((Ξ.card : ℝ) * (δ * S ^ ((1 : ℝ) / 2))) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, hE2]; ring
      _ ≤ S * T := this
  rcases hS.eq_or_lt with h0 | hSpos
  · -- S = 0 forces Xi empty
    have hempty : Ξ = ∅ := by
      by_contra hne
      obtain ⟨ξ, hξ⟩ := nonempty_iff_ne_empty.mpr hne
      have hz : (∑ ξ ∈ Ξ, ‖F ξ‖) ^ 2 ≤ 0 := by rw [← h0, zero_mul] at hmain; exact hmain
      have hpos : 0 < ‖F ξ‖ := by
        have := hΞ ξ hξ
        rw [← h0, Real.zero_rpow (by norm_num), mul_zero] at this
        exact this
      have hle : ‖F ξ‖ ≤ ∑ ξ ∈ Ξ, ‖F ξ‖ :=
        single_le_sum (f := fun ξ => ‖F ξ‖) (fun _ _ => norm_nonneg _) hξ
      nlinarith
    rw [hempty, card_empty, Nat.cast_zero, zero_mul]
    norm_num
    exact hT
  · rw [mul_comm S T] at hsq
    exact le_of_mul_le_mul_right hsq hSpos

/-- Final arithmetic: N^2 delta^2 at most K N^(1+eps') with eps' = eps/(2+eps) gives
N at most K^((2+eps)/2) delta^(-(2+eps)). -/
theorem level_set_arith {N δ K ε : ℝ} (hN : 0 ≤ N) (hδ : 0 < δ) (hK : 0 < K) (hε : 0 < ε)
    (h : (N * δ) ^ 2 ≤ K * N ^ (1 + ε / (2 + ε))) :
    N ≤ K ^ ((2 + ε) / 2) * δ ^ (-(2 + ε)) := by
  have hR : 0 ≤ K ^ ((2 + ε) / 2) * δ ^ (-(2 + ε)) :=
    mul_nonneg (Real.rpow_nonneg hK.le _) (Real.rpow_nonneg hδ.le _)
  rcases hN.eq_or_lt with h0 | hNpos
  · rw [← h0]; exact hR
  set e := ε / (2 + ε) with he
  have h2e : 0 < 2 + ε := by linarith
  have hsplit : N ^ (2 : ℝ) = N ^ (1 + e) * N ^ (1 - e) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hNe : 0 < N ^ (1 + e) := Real.rpow_pos_of_pos hNpos _
  have h1 : N ^ (1 - e) * δ ^ 2 ≤ K := by
    have : N ^ (1 + e) * (N ^ (1 - e) * δ ^ 2) ≤ N ^ (1 + e) * K := by
      have hh : (N * δ) ^ 2 = N ^ (2 : ℝ) * δ ^ 2 := by
        rw [mul_pow, Real.rpow_two]
      rw [hh, hsplit] at h
      linarith
    exact le_of_mul_le_mul_left this hNe
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h2 : N ^ (1 - e) ≤ K * δ ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hδ.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ hδ2]
    exact h1
  have hp : 0 < (2 + ε) / 2 := by positivity
  have h1e : (1 - e) * ((2 + ε) / 2) = 1 := by
    rw [he]; field_simp; ring
  have h3 := Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) h2 hp.le
  rw [← Real.rpow_mul hNpos.le, h1e, Real.rpow_one,
    Real.mul_rpow hK.le (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le] at h3
  have : -(2 : ℝ) * ((2 + ε) / 2) = -(2 + ε) := by ring
  rw [this] at h3
  exact h3

/-- Exactly the statement of paper_level_set_large_delta, from the duality step, display 4.2 of
Green and Tao and the final arithmetic. The exponent c is 1; the bound holds for every delta.
CONDITIONAL ON gt42_small_set. -/
theorem paper_level_set_large_delta_of_leaves (A D : ℝ → ℝ)
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
  intro ε hε
  have he : 0 < ε / (2 + ε) := by positivity
  obtain ⟨K, hK, H⟩ := gt42_all A D hAD (ε / (2 + ε)) he
  refine ⟨1, one_pos, K ^ ((2 + ε) / 2), Real.rpow_pos_of_pos hK _, ?_⟩
  intro J w hJ hw b hb hbW ham M hM hEB a δ hδ _
  set Ξ := (range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖) with hΞ
  obtain ⟨f, hf, hdual⟩ := level_set_duality M hM (restrictionBeta w (WW J w) b M)
    (restrictionBeta_nonneg w (WW J w) b M) a δ hδ Ξ (fun ξ hξ => (mem_filter.mp hξ).2)
  have hg := H J w hJ hw b hb hbW ham M hM hEB Ξ (filter_subset _ _) f hf
  exact level_set_arith (Nat.cast_nonneg _) hδ hK hε (hdual.trans hg)

/-- Twin check: the assembled theorem has exactly the type of the original LEAF. -/
theorem paper_level_set_large_delta_twin :
    type_of% @LeanLab.Teravainen2016.paper_level_set_large_delta :=
  paper_level_set_large_delta_of_leaves

end LeanLab.Teravainen2016.LevelSet1122b

#print axioms LeanLab.Teravainen2016.LevelSet1122b.dual_parseval
#print axioms LeanLab.Teravainen2016.LevelSet1122b.gt42_large_set
#print axioms LeanLab.Teravainen2016.LevelSet1122b.gt42_all
#print axioms LeanLab.Teravainen2016.LevelSet1122b.level_set_duality
#print axioms LeanLab.Teravainen2016.LevelSet1122b.level_set_arith
#print axioms LeanLab.Teravainen2016.LevelSet1122b.paper_level_set_large_delta_of_leaves
#print axioms LeanLab.Teravainen2016.LevelSet1122b.paper_level_set_large_delta_twin
