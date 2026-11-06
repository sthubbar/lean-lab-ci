/-
P0093 pages 162 and 163 equations 7.8 through 7.11.
Close finite phase concentration from weighted rotation and consecutive deficits.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Weighted439
import LeanLab.Linnik1951.PhaseCount439

namespace LeanLab.Linnik1951

open Finset

/-- P0093 pages 162 and 163 equations 7.8 through 7.11. A large
finite damped polynomial gives a small sum of unrotated cosine deficits.
All retained weights lie between exp of negative one and one. -/
theorem finite_cosine_deficit439 (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 ≤ η)
    (α : ℝ) (hlarge : (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖) :
    (∑ m ∈ range (Nat.log 2 N),
      (1 - Real.cos (2 * Real.pi * (α * (2 : ℝ) ^ (m + 1))))) ≤
        4 * (η * (Nat.log 2 N : ℝ) / Real.exp (-1)) + 2 := by
  let M := Nat.log 2 N
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let z : ℕ → ℂ := fun m => LeanLab.Linnik.Gallagher1975Lemma1.e
    (-α * (2 : ℝ) ^ (m + 1))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha (m : ℕ) (hm : m ∈ range M) : Real.exp (-1) ≤ a m := by
    apply Real.exp_le_exp.mpr
    have hp : 2 ^ (m + 1) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.mp hm)).trans
        (Nat.pow_log_le_self 2 (show N ≠ 0 by omega))
    have hdiv : (((2 ^ (m + 1) : ℕ) : ℝ) / N) ≤ 1 :=
      (div_le_one hNp).mpr (by exact_mod_cast hp)
    simpa only [neg_div] using neg_le_neg hdiv
  have ha1 (m : ℕ) (hm : m ∈ range M) : a m ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg N)
  have hz (m : ℕ) : ‖z m‖ = 1 := LeanLab.Linnik.Gallagher1975Lemma1.norm_e _
  have hstep (m : ℕ) : z (m + 1) = z m ^ 2 := by
    dsimp [z]
    rw [← LeanLab.Linnik.Gallagher1975Lemma1.e_two_mul]
    congr 1
    rw [pow_succ]
    ring
  have hzero : ‖powerTrunc412 N 0‖ = ∑ m ∈ range M, a m := by
    have heq : powerTrunc412 N 0 = ((∑ m ∈ range M, a m : ℝ) : ℂ) := by
      simp [powerTrunc412, a, M, Complex.ofReal_sum]
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun m hm => (Real.exp_pos _).le))]
  have hsum : powerTrunc412 N α = ∑ m ∈ range M, (a m : ℂ) * z m := by
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [a, z, LeanLab.Linnik.Gallagher1975Lemma1.e]
    congr 1
    congr 1
    push_cast
    ring
  have hlarge' : (1 - η) * (∑ m ∈ range M, a m) <
      ‖∑ m ∈ range M, (a m : ℂ) * z m‖ := by
    rw [← hzero, ← hsum]
    exact hlarge
  obtain ⟨w, hw, hdef⟩ := weighted_rotation_deficit439 M a z (Real.exp (-1)) η
    (Real.exp_pos _) hη ha ha1 hz hlarge'
  have hRe (m : ℕ) : (z m).re = Real.cos (2 * Real.pi * (α * (2 : ℝ) ^ (m + 1))) := by
    dsimp [z]
    rw [LeanLab.Linnik.Gallagher1975Lemma1.re_e,
      show 2 * Real.pi * (-α * (2 : ℝ) ^ (m + 1)) =
        -(2 * Real.pi * (α * (2 : ℝ) ^ (m + 1))) by ring, Real.cos_neg]
  have hd := consecutive_phase_deficit_sum439 M w hw z hz hstep
  simp_rw [hRe] at hd
  exact hd.trans (by linarith)

/-- P0093 page 162 equations 7.8 and 7.9 and page 163 through 7.11.
Exact finite_phase_concentration412 statement. A sufficiently small
large value margin and sufficiently long binary length absorb the last
phase and force every prescribed fraction and binary radius. -/
theorem finite_phase_concentration_proved439 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (r : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ α : ℝ, α ∈ Set.Icc (-1) 2 →
        (1 - η) * ‖powerTrunc412 N 0‖ < ‖powerTrunc412 N α‖ →
          (1 - ε) * (Nat.log 2 N : ℝ) ≤
            (nearIntegerIndices412 (Nat.log 2 N) r α).card := by
  let R := (1 / 2 : ℝ) ^ r
  let c := Real.exp (-1)
  let η := min (1 / 4 : ℝ) (ε * c * R ^ 2 / 4)
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : 0 < c := Real.exp_pos _
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηhalf : η < 1 / 2 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hηsmall : η ≤ ε * c * R ^ 2 / 4 := min_le_right _ _
  obtain ⟨M0, hM0⟩ := exists_nat_gt (2 / (ε * R ^ 2))
  refine ⟨η, hη, hηhalf, max 1 (2 ^ M0), ?_⟩
  intro N hN α hα hlarge
  have hN1 : 1 ≤ N := by have := le_max_left 1 (2 ^ M0); omega
  have hpow : 2 ^ M0 ≤ N := by have := le_max_right 1 (2 ^ M0); omega
  have hM : M0 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hpow
  have hMR : (M0 : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hM
  have hMp : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  have hlargeM : 2 ≤ ε * R ^ 2 * (Nat.log 2 N : ℝ) := by
    have hh := (div_lt_iff₀ (by positivity : 0 < ε * R ^ 2)).mp hM0
    nlinarith [mul_le_mul_of_nonneg_left hMR (show 0 ≤ ε * R ^ 2 by positivity)]
  have hsmall : 4 * (η * (Nat.log 2 N : ℝ) / c) ≤
      ε * R ^ 2 * (Nat.log 2 N : ℝ) := by
    rw [show 4 * (η * (Nat.log 2 N : ℝ) / c) =
      (4 * η * (Nat.log 2 N : ℝ)) / c by ring]
    apply (div_le_iff₀ hc).mpr
    have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hηsmall
    have hm := mul_le_mul_of_nonneg_right hh hMp
    nlinarith
  have hd := finite_cosine_deficit439 N hN1 η hη.le α hlarge
  have hb := bad_phase_card439 (Nat.log 2 N) r α
  change ((Nat.log 2 N : ℝ) - (nearIntegerIndices412 (Nat.log 2 N) r α).card) *
    (8 * R ^ 2) ≤ _ at hb
  have hbound : ((Nat.log 2 N : ℝ) - (nearIntegerIndices412 (Nat.log 2 N) r α).card) *
      (8 * R ^ 2) ≤ (ε * (Nat.log 2 N : ℝ)) * (8 * R ^ 2) := by
    change _ ≤ 4 * (η * (Nat.log 2 N : ℝ) / c) + 2 at hd
    nlinarith
  have hcancel := le_of_mul_le_mul_right hbound (show 0 < 8 * R ^ 2 by positivity)
  nlinarith

end LeanLab.Linnik1951
