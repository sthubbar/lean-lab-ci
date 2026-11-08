import LeanLab.KumchevLiu2007.SPLIT_kumchev_liu_thm2_03275_target

/-!
The unrestricted epsilon in the sealed sieve input admits unit intervals.
This contradicts the existing square exception family.
Source: arXiv:0801.0130 page 19 display 68 requires theta2 greater than 7/12.
The witness epsilon = 119/400 instead gives theta2 = 0.
This is a question about the formal leaf. It does not refute Theorem 2.
AI wrote the Lean code. Goldbach is open.
-/

open Classical
namespace LeanLab.KumchevLiu2007.Task456
open Novelty1612

/-- LEAF. Negation of the exact sealed sieve input. Page 19 display 68 has a
positive lower restriction on theta2. The formal input omits that restriction.
At epsilon = 119/400 and H = 1 it would remove every sufficiently large
square exception derived from the page 1 definition of H2. -/
theorem not_sieve_inputs_03275 :
    ¬ (∀ A : ℝ, 0 < A → ∀ ε : ℝ, 0 < ε → ∃ C X0 K δ : ℝ, δ < 1 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ ((55 / 100 + ε) * (595 / 1000 - 2 * ε)) ≤ H → H ≤ X →
        ∃ (Rv R0 M : ℕ → ℝ) (B1 B2 : ℕ → Prop),
          (cntIoc B1 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
          (cntIoc B2 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
          (∀ n, InH2 n → ¬ B1 n → 0 < M n ∧ 16 / 100 * M n ≤ Rv n) ∧
          (∀ n, InH2 n → ¬ B2 n → R0 n ≤ K * M n * Real.log X ^ (δ - 1)) ∧
          (∀ n, InH2 n → 0 < Rv n - R0 n → IsPrimePlusPrimeSq n)) := by
  classical
  intro hs
  obtain ⟨C, X0, K, δ, hδ, hs⟩ := hs 1 (by norm_num) (119 / 400) (by norm_num)
  obtain ⟨L0, hL0, hsave⟩ := saving_beats_constant K δ hδ
  let T : ℝ := max X0 (max 2 (Real.exp (max L0 (C + 1))))
  obtain ⟨t, ht⟩ := exists_nat_gt T
  let n : ℕ := (30 * (t + 1) + 6) ^ 2
  let X : ℝ := (n : ℝ) - 1
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have htX : (t : ℝ) ≤ X := by
    dsimp [X, n]
    push_cast
    nlinarith
  have hTX : T < X := lt_of_lt_of_le ht htX
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hTX.le
  have hX2 : 2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTX.le
  have hXe : Real.exp (max L0 (C + 1)) < X :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hTX
  have hlog : max L0 (C + 1) < Real.log X := by
    rw [← Real.log_exp (max L0 (C + 1))]
    exact Real.log_lt_log (Real.exp_pos _) hXe
  have hlog0 : 0 < Real.log X := lt_trans hL0 (lt_of_le_of_lt (le_max_left _ _) hlog)
  have hC : C < Real.log X := by
    have := lt_of_le_of_lt (le_max_right _ _) hlog
    linarith
  have hrange : X ^ ((55 / 100 + (119 : ℝ) / 400) *
      (595 / 1000 - 2 * (119 / 400))) ≤ 1 := by norm_num
  obtain ⟨Rv, R0, M, B1, B2, hB1, hB2, hmain, hsecondary, hrep⟩ :=
    hs X 1 hX0 hrange (by linarith)
  have hsmall : C * 1 / Real.log X ^ (1 : ℝ) < 1 := by
    rw [Real.rpow_one, mul_one]
    exact (div_lt_one hlog0).2 hC
  have hnotbad : ∀ B : ℕ → Prop,
      (cntIoc B X 1 : ℝ) ≤ C * 1 / Real.log X ^ (1 : ℝ) → ¬ B n := by
    intro B hB hn
    have hmem : n ∈ (Finset.range (⌊X + 1⌋₊ + 1)).filter
        (fun m : ℕ => X < (m : ℝ) ∧ B m) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_, hn⟩
      · exact Nat.lt_succ_of_le (Nat.le_floor (by dsimp [X]; linarith))
      · dsimp [X]
        linarith
    have hcount : 1 ≤ cntIoc B X 1 := Finset.one_le_card.mpr ⟨n, hmem⟩
    have hcountR : (1 : ℝ) ≤ cntIoc B X 1 := by exact_mod_cast hcount
    linarith
  have hnH : InH2 n := inH2_family (t + 1)
  obtain ⟨hM, hRv⟩ := hmain n hnH (hnotbad B1 hB1)
  have hR0 := hsecondary n hnH (hnotbad B2 hB2)
  have hsaveX := hsave (Real.log X) (le_trans (le_max_left _ _) hlog.le)
  have hR0' : R0 n ≤ 1 / 20 * M n := by
    calc
      R0 n ≤ K * M n * Real.log X ^ (δ - 1) := hR0
      _ = (K * Real.log X ^ (δ - 1)) * M n := by ring
      _ ≤ 1 / 20 * M n := mul_le_mul_of_nonneg_right hsaveX hM.le
  exact not_form_family (Nat.succ_le_succ (Nat.zero_le t))
    (hrep n hnH (by linarith))

end LeanLab.KumchevLiu2007.Task456

#print axioms LeanLab.KumchevLiu2007.Task456.not_sieve_inputs_03275
