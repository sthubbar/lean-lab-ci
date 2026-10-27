/-
AI-written Lean code, Codex task05, 2026-10-22.
Quantitative tails of the twin-pair reciprocal series.
These constants are lab consequences of the explicit Selberg count bound.
They are not printed constants from the inaccessible 1919 scan.
-/
import LeanLab.Brun1919.SharperUpper
import LeanLab.Brun1919.Final

open Finset

noncomputable section
namespace LeanLab.Brun1919

/-- A reciprocal-square term is bounded by a telescoping reciprocal difference. -/
lemma reciprocal_square_le_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hxp : 0 < x + 1 := by linarith
  calc
    1 / (x + 1) ^ 2 ≤ 1 / (x * (x + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = 1 / x - 1 / (x + 1) := by
      field_simp
      <;> ring

/-- A finite union of dyadic blocks has an explicit telescoping reciprocal bound. -/
lemma dyadic_reciprocal_tail_partial (K M : ℕ) (hK : 1 ≤ K) :
    (∑ p ∈ Ico (2 ^ K) (2 ^ (K + M)),
      if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) ≤
        (4096 / Real.log 2 ^ 2) * (1 / (K : ℝ) - 1 / ((K + M : ℕ) : ℝ)) := by
  let f : ℕ → ℝ := fun p => if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0
  let B : ℝ := 4096 / Real.log 2 ^ 2
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hK0 : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  change (∑ p ∈ Ico (2 ^ K) (2 ^ (K + M)), f p) ≤
    B * (1 / (K : ℝ) - 1 / ((K + M : ℕ) : ℝ))
  induction M with
  | zero => simp
  | succ M ih =>
    have hlo : 2 ^ K ≤ 2 ^ (K + M) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi : 2 ^ (K + M) ≤ 2 ^ (K + M + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hstep : (∑ p ∈ Ico (2 ^ (K + M)) (2 ^ (K + M + 1)), f p) ≤
        B * (1 / (((K + M : ℕ) : ℝ) + 1) ^ 2) := by
      have hb := block_le twinCount_le_1024 (by norm_num : (0 : ℝ) ≤ 1024) (K + M)
      norm_num [f, B] at hb ⊢
      exact hb
    have hk0 : 0 < ((K + M : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < K + M)
    have hr := reciprocal_square_le_step ((K + M : ℕ) : ℝ) hk0
    have hstep' : (∑ p ∈ Ico (2 ^ (K + M)) (2 ^ (K + M + 1)), f p) ≤
        B * (1 / ((K + M : ℕ) : ℝ) - 1 / (((K + M : ℕ) : ℝ) + 1)) := by
      calc
        _ ≤ B * (1 / (((K + M : ℕ) : ℝ) + 1) ^ 2) := hstep
        _ ≤ _ := by gcongr
    have hsplit := (sum_Ico_consecutive f hlo hhi).symm
    rw [show K + M.succ = K + M + 1 by omega, hsplit]
    push_cast at ih hstep' ⊢
    nlinarith

/-- An explicit upper bound for the entire reciprocal tail above a dyadic cutoff. -/
theorem brun_tail_bound (K : ℕ) (hK : 1 ≤ K) :
    (∑' p : ℕ, if 2 ^ K ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) ≤
      (4096 / Real.log 2 ^ 2) / (K : ℝ) := by
  let f : ℕ → ℝ := fun p => if IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0
  let g : ℕ → ℝ := fun p => if 2 ^ K ≤ p then f p else 0
  let B : ℝ := 4096 / Real.log 2 ^ 2
  have hf0 : ∀ p, 0 ≤ f p := by intro p; dsimp [f]; split_ifs <;> positivity
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    split_ifs
    · exact hf0 p
    · exact le_rfl
  have heq : ∀ p : ℕ,
      (if 2 ^ K ≤ p ∧ IsTwin p then (1 : ℝ) / p + 1 / (p + 2) else 0) = g p := by
    intro p
    dsimp [g, f]
    split_ifs <;> simp_all
  calc
    _ = ∑' p : ℕ, g p := tsum_congr heq
    _ ≤ B / (K : ℝ) := by
      apply Real.tsum_le_of_sum_range_le hg0
      intro n
      have hbig : n ≤ 2 ^ (K + n) :=
        (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hsum : (∑ p ∈ range n, g p) ≤ ∑ p ∈ range (2 ^ (K + n)), g p :=
        sum_le_sum_of_subset_of_nonneg (range_mono hbig) (fun p _ _ => hg0 p)
      have hpow : 2 ^ K ≤ 2 ^ (K + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hlow : (∑ p ∈ range (2 ^ K), g p) = 0 := by
        apply sum_eq_zero
        intro p hp
        simp [g, not_le.mpr (mem_range.mp hp)]
      have hmid : (∑ p ∈ range (2 ^ (K + n)), g p) =
          ∑ p ∈ Ico (2 ^ K) (2 ^ (K + n)), f p := by
        rw [← sum_range_add_sum_Ico g hpow, hlow, zero_add]
        apply sum_congr rfl
        intro p hp
        exact if_pos (mem_Ico.mp hp).1
      have hp := dyadic_reciprocal_tail_partial K n hK
      have hB0 : 0 ≤ B := by dsimp [B]; positivity
      have hterm : 0 ≤ 1 / (((K + n : ℕ) : ℝ)) := by positivity
      calc
        (∑ p ∈ range n, g p) ≤ ∑ p ∈ range (2 ^ (K + n)), g p := hsum
        _ = ∑ p ∈ Ico (2 ^ K) (2 ^ (K + n)), f p := hmid
        _ ≤ B * (1 / (K : ℝ) - 1 / ((K + n : ℕ) : ℝ)) := hp
        _ ≤ B / (K : ℝ) := by
          calc
            _ ≤ B * (1 / (K : ℝ)) :=
              mul_le_mul_of_nonneg_left (sub_le_self _ hterm) hB0
            _ = B / (K : ℝ) := by ring

#print axioms brun_tail_bound

#print axioms dyadic_reciprocal_tail_partial

#print axioms reciprocal_square_le_step

end LeanLab.Brun1919
