/- AI wrote this Lean code for CODEX task327. Goldbach is open.
Supply the exact sealed lower model from finite expansion, scalar delay sums
and the signed stopping error. BJS v6 Section 2.4, pp. 10 to 16.
The selected table constants are from BJS v2 p. 5 and journal p. 1218.
https://arxiv.org/abs/2207.09452v6 -/
import LeanLab.BS2022GRH.Decomp327a

namespace LeanLab.BS2022GRH.Decomp327c
open Real Finset Classical ChenThresholdGRH Decomp148f DecompC169d Decomp327a
noncomputable section

/-- LEAF. The lower parity stopping error after subtracting each main term.
BJS p. 11 display 33, p. 14 Proposition 13, p. 15 Lemma 14.
Journal p. 1218 Table 1 row 6100 supplies constant 114 at epsilon one over 8349.
This contains neither the leading scalar normalization nor the model expansion,
sequence aggregation or exceptional Euler factors. It bounds only the error. -/
theorem lower_stopping_error (P : Set ℕ) (Q : Finset ℕ) (g : ℕ → ℝ) (z D : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hz : 2 ≤ z)
    (hprod : ∀ u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (∑ n ∈ range ((siftingPrimes P z \ Q).card + 3),
      if 0 < n ∧ n % 2 = 0 then
        stoppingTerm (siftingPrimes P z \ Q) D g n -
          (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) * delayTerm n (log D / log z)
      else 0) ≤
      (∏ p ∈ siftingPrimes P z \ Q, (1 - g p)) *
        ((1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) := by
  sorry

/-- The exact sealed lower model statement follows from the smaller source leaves.
CONDITIONAL ON stopping_expansion, delay_partial_sums and lower_stopping_error.
No use of either original model sorry. Journal pp. 1218 and 1219. -/
theorem rosser_lower_model (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
        (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z ≤
        weightedModel supp a P Q g z D (rosserSubsetWeight P Q z D false)  := by
  apply rosser_model_lower_of_prime supp a P Q g z D _
    ha hP hQ hz (le_trans (by nlinarith : z ≤ z ^ 2) hzD)
  intro m hm
  apply lower_transfer _ _ _ _ _
    (fun p hp => (hg m p (mem_filter.mp hp).2.1).2.le)
  let S := siftingPrimes P z \ Q
  have hp : ∀ p ∈ S, p.Prime := fun p hp =>
    hP p (mem_filter.mp (mem_sdiff.mp hp).1).2.1
  have hzpos : 0 < z := by linarith
  have hlz : 0 < log z := log_pos (by linarith)
  have hD : 1 < D := by nlinarith
  have hslo : (2 : ℝ) ≤ log D / log z := by
    apply (le_div_iff₀ hlz).2
    have hh := log_le_log ((pow_pos hzpos 2)) hzD
    rw [log_pow] at hh
    norm_num at hh
    linarith
  have hv : 0 ≤ ∏ p ∈ S, (1 - g m p) := by
    apply prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hg m p (mem_filter.mp (mem_sdiff.mp hp).1).2.1).2.le
  have he := (stopping_expansion S D (g m) hp hD).2
  have herr := lower_stopping_error P Q (g m) z D hP (hg m) hz
    (hprod m) hzD hs
  have hf := (delay_partial_sums (log D / log z) (S.card + 3)).2 hslo hs
  have hmain := mul_le_mul_of_nonneg_left hf hv
  have hsplit :
      (∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then
        stoppingTerm S D (g m) n - (∏ p ∈ S, (1 - g m p)) * delayTerm n (log D / log z)
        else 0) =
      (∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then stoppingTerm S D (g m) n else 0) -
        (∏ p ∈ S, (1 - g m p)) *
          ∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then delayTerm n (log D / log z) else 0 := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> ring
  change (∑ n ∈ range (S.card + 3), if 0 < n ∧ n % 2 = 0 then
    stoppingTerm S D (g m) n - (∏ p ∈ S, (1 - g m p)) * delayTerm n (log D / log z)
    else 0) ≤ _ at herr
  rw [hsplit] at herr
  change _ ≤ rosserPrimeModel S ∅ D false (g m) 
  rw [he]
  linear_combination herr + hmain

#print axioms lower_stopping_error
#print axioms rosser_lower_model

end
end LeanLab.BS2022GRH.Decomp327c
