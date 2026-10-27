/-
Li and Liu, https://arxiv.org/pdf/2610.15784, page 4 display 11 and page 21 before Lemma 7.1.
Normalized signed first moments from the lab's unconditional PNT window.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Task37Lemma71Integral

namespace LeanLab.Linnik.Task37FirstMoments
open Set Real Finset Filter Topology
open LeanLab.Linnik.U1426ChainWire
open LeanLab.Linnik.U1429Display58
open LeanLab.Linnik.U1434Lemma21
open LeanLab.Linnik.Task37Lemma71
open LeanLab.Linnik.LiLiuDisplay37 (primesIn)

theorem sum_UN_rj_ge (j N1 N L : ℕ) (hj : j ≤ 3) :
    (L : ℝ) ^ j * (Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) -
      Chebyshev.theta ((max N1 2 : ℕ) : ℝ)) ≤ ∑ n ∈ UN N, rj j N1 N L n := by
  rw [sum_UN_rj]
  have hnn : 0 ≤ ∑ p ∈ primesIn N1 N, ∑ ν : Fin j → Fin L,
      (if p + sv ν ∈ UN N then Real.log p else 0) :=
    sum_nonneg fun p _ => sum_nonneg fun ν _ => by
      split_ifs
      · exact Real.log_natCast_nonneg p
      · exact le_rfl
  by_cases hMK : max N1 2 ≤ N - (3 * 2 ^ L + 1)
  · rw [← LiLiuDisplay37.sum_primesIn hMK, mul_sum]
    calc _ = ∑ p ∈ primesIn (max N1 2) (N - (3 * 2 ^ L + 1)), ∑ ν : Fin j → Fin L,
          (if p + sv ν ∈ UN N then Real.log p else 0) := by
          refine sum_congr rfl fun p hp => ?_
          simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp
          have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.2.odd_of_ne_two (by omega))
          have hin : ∀ ν : Fin j → Fin L, p + sv ν ∈ UN N := fun ν => by
            have h1 := (sv_le ν).trans (Nat.mul_le_mul_right (2 ^ L) hj)
            have h2 := sv_even ν
            simp only [UN, Finset.mem_filter, Finset.mem_range]; omega
          simp_rw [ite_eq_left (hin _)]
          rw [sum_const, card_fun, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => sum_nonneg fun ν _ => by
            split_ifs
            · exact Real.log_natCast_nonneg p
            · exact le_rfl
          intro p hp
          simp only [primesIn, Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
          exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · have : Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) ≤
        Chebyshev.theta ((max N1 2 : ℕ) : ℝ) :=
      Chebyshev.theta_mono (by exact_mod_cast (show N - (3 * 2 ^ L + 1) ≤ max N1 2 by omega))
    have h2 : (L : ℝ) ^ j * (Chebyshev.theta ((N - (3 * 2 ^ L + 1) : ℕ) : ℝ) -
        Chebyshev.theta ((max N1 2 : ℕ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith


noncomputable def mass (j : ℕ) (κ : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ UN N, rj j (N1f κ N) N (Lfun N) n) / (N * (Lfun N : ℝ) ^ j)

/-- The first moments of display 11, including the harmless zero exponent case. -/
theorem mass_tendsto {κ : ℝ} (hκ : 0 < κ) (j : ℕ) (hj : j ≤ 3) :
    Tendsto (mass j κ) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η : ℝ := min (ε / 2) (1 / 2)
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  filter_upwards [pnt_window hκ hη0 hη1, eventually_Lfun_ge_one, eventually_ge_atTop 1]
    with N hp hL hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLr : (0 : ℝ) < Lfun N := by exact_mod_cast hL
  have hd : 0 < (N : ℝ) * (Lfun N : ℝ) ^ j := by positivity
  have hlo := (mul_le_mul_of_nonneg_left hp.1 (pow_nonneg (Nat.cast_nonneg (Lfun N)) j)).trans
    (sum_UN_rj_ge j (N1f κ N) N (Lfun N) hj)
  have hhi := (sum_UN_rj_le j (N1f κ N) N (Lfun N)).trans
    (mul_le_mul_of_nonneg_left hp.2 (pow_nonneg (Nat.cast_nonneg (Lfun N)) j))
  have hlow : 1 - η ≤ mass j κ N := by
    unfold mass
    rw [le_div_iff₀ hd]
    nlinarith
  have hhigh : mass j κ N ≤ 1 + η := by
    unfold mass
    rw [div_le_iff₀ hd]
    nlinarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

noncomputable def combined (a b c τ κ : ℝ) (N : ℕ) : ℝ :=
  mass 2 κ N - c * mass 1 κ N + τ * (mass 3 κ N - a * mass 2 κ N - b * mass 1 κ N)

lemma combined_tendsto {κ : ℝ} (hκ : 0 < κ) (a b c τ : ℝ) :
    Tendsto (combined a b c τ κ) atTop (𝓝 (1 - c + τ * (1 - a - b))) := by
  unfold combined
  simpa only [mul_one] using
    (((mass_tendsto hκ 2 (by norm_num)).sub ((mass_tendsto hκ 1 (by norm_num)).const_mul c)).add
    ((((mass_tendsto hκ 3 (by norm_num)).sub ((mass_tendsto hκ 2 (by norm_num)).const_mul a)).sub
      ((mass_tendsto hκ 1 (by norm_num)).const_mul b)).const_mul τ))

/-- The normalized combination is the weighted signed first moment used in Lemma 7.1. -/
lemma combined_eq (a b c τ κ : ℝ) {N : ℕ} (hN : 0 < N) (hL : 0 < Lfun N) :
    combined a b c τ κ N =
      ((Lfun N : ℝ) * ∑ n ∈ UN N, f2 c (N1f κ N) N (Lfun N) n +
        τ * ∑ n ∈ UN N, ff a b (N1f κ N) N (Lfun N) n) /
        (N * (Lfun N : ℝ) ^ 3) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hLr : (Lfun N : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold combined mass f2 ff
  simp only [sum_sub_distrib, ← mul_sum]
  field_simp

/-- A concrete positive cutoff parameter for the first moment limits. -/
theorem mass_half : Tendsto (mass 2 (1 / 2)) atTop (𝓝 1) :=
  mass_tendsto (by norm_num) 2 (by norm_num)

end LeanLab.Linnik.Task37FirstMoments

#print axioms LeanLab.Linnik.Task37FirstMoments.sum_UN_rj_ge
#print axioms LeanLab.Linnik.Task37FirstMoments.mass_tendsto
#print axioms LeanLab.Linnik.Task37FirstMoments.combined_tendsto
#print axioms LeanLab.Linnik.Task37FirstMoments.combined_eq
#print axioms LeanLab.Linnik.Task37FirstMoments.mass_half
