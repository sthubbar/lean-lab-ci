import LeanLab.LZCesaroShort.PrintedProps
import LeanLab.LZCesaroShort.Sec5One

/-!
# P0058 Theorem 1, the printed Prop `Theorem1P`, from RH

Lab proof, unit U-6211, CLOUD 20261020T0817Z-cloud38, T1. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only. Binary Goldbach is OPEN.

* `R_le`: `R(n) ≤ (n + 1) log² n`, elementary;
* `theorem1_H1`: Theorem 1 at `H = 1`, where `cesaro N 1 = R(N)`, from `sec5_rh_one`;
* `theorem1P_proved : RiemannHypothesis → Theorem1P`: the printed Theorem 1 for every `N ≥ 2`
  and `1 ≤ H ≤ N`, no restriction left;
* `cesaro_pos_RH`, `exists_R_pos_RH`: the links `cesaro_pos_of_printed` and
  `exists_R_pos_short_printed` of `Theorem1Printed.lean` now hold from RH alone.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

lemma vonMangoldt_le_log_of_le {a n : ℕ} (ha : a ≤ n) : Λ a ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · subst h0; simp only [ArithmeticFunction.map_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast ha))

/-- `R(n) ≤ (n + 1) log² n`. -/
lemma R_le (n : ℕ) : R n ≤ ((n : ℝ) + 1) * Real.log n ^ 2 := by
  unfold R
  have h : ∀ p ∈ antidiagonal n, Λ p.1 * Λ p.2 ≤ Real.log n ^ 2 := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h1 := vonMangoldt_le_log_of_le (a := p.1) (n := n) (by omega)
    have h2 := vonMangoldt_le_log_of_le (a := p.2) (n := n) (by omega)
    have := ArithmeticFunction.vonMangoldt_nonneg (n := p.1)
    have := ArithmeticFunction.vonMangoldt_nonneg (n := p.2)
    rw [sq]; exact mul_le_mul h1 h2 (by assumption) (le_trans (by assumption) h1)
  refine (sum_le_sum h).trans (le_of_eq ?_)
  rw [sum_const, Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring

/-- **P0058 Theorem 1 at `H = 1`, under RH.** -/
theorem theorem1_H1 (hRH : RiemannHypothesis) : ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ‖((cesaro N 1 : ℝ) : ℂ) - ((1 : ℕ) : ℂ) * N + 2 / ((1 : ℕ) : ℂ) * ZH N 1‖
      ≤ K * (N * Real.log (2 * (N : ℝ) / (1 : ℕ)) ^ 2) := by
  obtain ⟨N5, K5, h5⟩ := sec5_rh_one hRH
  refine ⟨3 + 4 * |K5|, max N5 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hz := h5 N 1 (le_trans (le_max_left _ _) hN) le_rfl (by omega)
  simp only [Nat.cast_one, div_one, one_mul, mul_one] at hz ⊢
  rw [cesaro_one (by omega)]
  set L := Real.log (2 * (N : ℝ)) with hL
  have hlN : Real.log N ≤ L := Real.log_le_log hN0 (by linarith)
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 1 ≤ 2 * (N : ℝ) := by linarith
    exact (Real.le_log_iff_exp_le (by positivity)).mpr this
  have hsN : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hR := R_le N
  have hR0 := R_nonneg N
  have hK5 : K5 * (Real.sqrt N * Real.log N ^ 2 + N) ≤ |K5| * (2 * (N * L ^ 2)) := by
    have h1 : Real.sqrt N * Real.log N ^ 2 + N ≤ 2 * (N * L ^ 2) := by
      have : Real.log N ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlN0 hlN 2
      have : Real.sqrt N * Real.log N ^ 2 ≤ N * L ^ 2 :=
        mul_le_mul hsN this (by positivity) (by positivity)
      have : (N : ℝ) ≤ N * L ^ 2 := le_mul_of_one_le_right hN0.le (by nlinarith)
      linarith
    calc K5 * (Real.sqrt N * Real.log N ^ 2 + N) ≤ |K5| * (Real.sqrt N * Real.log N ^ 2 + N) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have htri : ‖((R N : ℝ) : ℂ) - (N : ℂ) + 2 * ZH N 1‖ ≤ R N + N + 2 * ‖ZH N 1‖ := by
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((R N : ℝ) : ℂ) (N : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0, Complex.norm_natCast] at this
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  refine htri.trans ?_
  have hRL : R N ≤ 2 * (N * L ^ 2) := by
    have : Real.log N ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlN0 hlN 2
    have : ((N : ℝ) + 1) * Real.log N ^ 2 ≤ 2 * N * L ^ 2 :=
      mul_le_mul (by linarith) this (sq_nonneg _) (by positivity)
    linarith
  have hNL : (N : ℝ) ≤ N * L ^ 2 := le_mul_of_one_le_right hN0.le (by nlinarith)
  nlinarith [abs_nonneg K5]

/-- **P0058 Theorem 1, the printed Prop, from RH.** -/
theorem theorem1P_proved (hRH : RiemannHypothesis) : Theorem1P := by
  obtain ⟨K1, N1, h1⟩ := theorem1_H1 hRH
  obtain ⟨K2, N2, h2⟩ := theorem1_full hRH
  set g : ℕ → ℕ → ℝ := fun N H =>
    N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H) with hg
  have hgpos : ∀ N H, 2 ≤ N → 1 ≤ H → H ≤ N → 0 < g N H := by
    intro N H hN hH hHN
    have := log_two_N_div_pos hN hH hHN
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by
      have : (1 : ℝ) ≤ 2 * H := by
        have : (1 : ℝ) ≤ H := by exact_mod_cast hH
        linarith
      have := Real.log_nonneg this
      positivity
    simp only [hg]; positivity
  have hK : ∀ N H, max N1 N2 ≤ N → 1 ≤ H → H ≤ N →
      ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖ ≤ (|K1| + |K2|) * g N H := by
    intro N H hN hH hHN
    have hN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
    have hN2 : N2 ≤ N := le_trans (le_max_right _ _) hN
    have hNN : 2 ≤ N ∨ N < 2 := le_or_gt 2 N
    have h0 : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by
      have : (1 : ℝ) ≤ 2 * H := by
        have : (1 : ℝ) ≤ H := by exact_mod_cast hH
        linarith
      have := Real.log_nonneg this
      have : 0 ≤ Real.log N ^ 2 := sq_nonneg _
      positivity
    have hm : 0 ≤ (N : ℝ) * Real.log (2 * (N : ℝ) / H) ^ 2 := by positivity
    rcases Nat.lt_or_ge H 2 with hH1 | hH2
    · have hHe : H = 1 := by omega
      subst hHe
      have := h1 N hN1
      refine this.trans ?_
      have : K1 * (N * Real.log (2 * (N : ℝ) / (1 : ℕ)) ^ 2) ≤ (|K1| + |K2|) * (N * Real.log (2 * (N : ℝ) / (1 : ℕ)) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self K1, abs_nonneg K2]) hm
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      simp only [hg]
      exact le_add_of_nonneg_right h0
    · refine (h2 N H hN2 hH2 hHN).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self K2, abs_nonneg K1])
        (add_nonneg hm h0)
  obtain ⟨K', hK'⟩ := absorb_small
    (fun N H => ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖) g 1 hgpos hK
  exact ⟨K', fun N H hN hH hHN => hK' N H hN hH hHN⟩

/-- **The unweighted Cesàro count is positive in every window `C log² N ≤ H ≤ N`, under RH.** -/
theorem cesaro_pos_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N → 0 < cesaro N H :=
  cesaro_pos_of_printed (theorem1P_proved hRH) (lz_sec5_rh_proved hRH)

/-- **Every window `C log² N ≤ H ≤ N` holds a sum of two prime powers, under RH.** -/
theorem exists_R_pos_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N H : ℕ, N₀ ≤ N → C * Real.log N ^ 2 ≤ H → H ≤ N →
      ∃ n ∈ Icc (N - H) (N + H), ∃ a b : ℕ, IsPrimePow a ∧ IsPrimePow b ∧ a + b = n :=
  exists_R_pos_short_printed hRH (theorem1P_proved hRH)

end LeanLab.LZCesaroShort

namespace LeanLab.LZCesaroShort

open Finset
open scoped ArithmeticFunction.vonMangoldt Chebyshev

/-- `|wsum N H y| ≤ Σ_{|n − N| ≤ H} |term n|`, uniformly in `y`. -/
lemma abs_wsum_le (N H : ℕ) (y : ℝ) :
    |wsum N H y| ≤ ∑ n ∈ Icc (N - H) (N + H),
      |Real.exp (-(n : ℝ) / N) * (R n - (2 * ψ n - n)) * w N H n| := by
  unfold wsum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)

/-- **P0058 Theorem 2 eq. (2), the stated Prop, from RH.** -/
theorem theorem2a_proved (hRH : RiemannHypothesis) : Theorem2a := by
  obtain ⟨K, hK0, h⟩ := theorem2a_full hRH
  set A : ℕ → ℕ → ℝ := fun N H => ∑ n ∈ Icc (N - H) (N + H),
      |Real.exp (-(n : ℝ) / N) * (R n - (2 * ψ n - n)) * w N H n| with hA
  set g : ℕ → ℕ → ℝ := fun N H => N * Real.log N ^ 2 * Real.log (2 * H) with hg
  have hgpos : ∀ N H, 2 ≤ N → 1 ≤ H → H ≤ N → 0 < g N H := by
    intro N H hN hH hHN
    have h1 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h2 : 0 < Real.log (2 * H) := Real.log_pos (by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      linarith)
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    simp only [hg]; positivity
  set N₀ : ℕ := 10 ^ 20 with hN₀
  obtain ⟨K', hK'⟩ := absorb_small (fun N H => if N < N₀ then A N H else 0) g 1 hgpos
    (K := 0) (N₀ := N₀) (fun N H hN _ _ => by simp [not_lt.mpr hN])
  refine ⟨max K K', fun N H hN hH hHN y hy0 hyH => ?_⟩
  have hg0 := hgpos N H hN hH hHN
  rcases lt_or_ge N N₀ with hs | hl
  · have h1 := hK' N H hN hH hHN
    simp only [hs, ite_true] at h1
    have h2 := (abs_wsum_le N H y).trans h1
    have : K' * g N H ≤ max K K' * g N H := mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le
    simp only [hg] at this h2
    nlinarith
  · have hN20 : (10 : ℝ) ^ 20 ≤ N := by
      have := (Nat.cast_le (α := ℝ)).mpr hl
      rw [hN₀, Nat.cast_pow] at this
      exact_mod_cast this
    have h1 := h N H y hN20 hH hHN hy0 hyH
    have : K * g N H ≤ max K K' * g N H := mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le
    simp only [hg] at this
    nlinarith

end LeanLab.LZCesaroShort
