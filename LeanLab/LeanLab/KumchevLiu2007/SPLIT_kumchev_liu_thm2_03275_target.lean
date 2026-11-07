import LeanLab.KumchevLiu2007.Novelty1612

/-!
SPLIT of `kumchev_liu_thm2_03275_target` into its proof steps.

The target is the sharpened exponent `0.3275` for the count of even `n` not congruent to `1` mod `3`
which are not a prime plus a square of a prime. The route to it is the endgame of the source's
Section 5 with the second sieve parameter left at `0.595` rather than raised to `3/5`:

* step 1, the parameter arithmetic: `(0.55 + ε)(0.595 - 2ε) < 0.3275` for every `ε > 0`;
* step 2, the range transfer: for `X ≥ 1` a lower exponent gives a lower power, so the sieve input
  is needed only in the range `X^(0.3275) ≤ H`;
* step 3, the saving `L^(δ-1)` with `δ < 1` beats any fixed constant;
* step 4, the circle method output in that range: the main term on the good set, the secondary term
  on the second bad set, both bad sets of size `≤ C H (log X)^(-A)`, and a positive difference of
  the two main terms forcing a representation.

Step 4 is the analytic input; the assembly below is purely bookkeeping over it and is where the
exceptions are covered by the union of the two bad sets.

The leaves carry `sorry`; the assembly `kumchev_liu_thm2_03275_target_split` has none.
AI-written Lean code. Checked only by the Lean kernel. Binary Goldbach is open.
-/

open Classical

namespace LeanLab.KumchevLiu2007.Novelty1612

/-- LEAF. Step 1 of the split of `kumchev_liu_thm2_03275_target`: the numerical parameter step. With
the second sieve exponent at `0.595 - 2 ε` instead of `3/5 - 2 ε`, the product with `0.55 + ε` stays
below `0.3275`, so the smaller exponent is all that the sharper parameter buys. -/
theorem theta_exponent_03275 {ε : ℝ} (hε : 0 < ε) :
    (55 / 100 + ε) * (595 / 1000 - 2 * ε) < 3275 / 10000 := by
  sorry

/-- LEAF. Step 2 of the split: the range transfer. For a base `X ≥ 1` a smaller exponent gives a
smaller power, so the hypothesis `X^c ≤ H` of the sieve input at `c = θ₁ θ₂` follows from the
hypothesis `X^(0.3275) ≤ H` used by the target. -/
theorem rpow_range_transfer {X θ c H : ℝ} (hX : 1 ≤ X) (hθc : θ ≤ c) (hH : X ^ c ≤ H) :
    X ^ θ ≤ H := by
  sorry

/-- LEAF. Step 3 of the split: a saving `L^(δ - 1)` with `δ < 1` beats any fixed constant, so the
secondary error term is at most a twentieth of the main term once `log X` exceeds a threshold. -/
theorem saving_beats_constant (K δ : ℝ) (hδ : δ < 1) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L → K * L ^ (δ - 1) ≤ 1 / 20 := by
  sorry

/-- LEAF. Step 4 of the split: the circle method output of Section 5 for this exponent, with the
second parameter at `0.595 - 2 ε`. Outside a first bad set the main term is positive and at least
`0.16` of it survives as the lower bound `Rv`; outside a second bad set the secondary term is at
most `K M (log X)^(δ-1)`; both bad sets are counted by at most `C H / (log X)^A` numbers in the
interval; and a positive difference `Rv - R0` forces a representation as a prime plus a square of a
prime. -/
theorem sieve_inputs_03275 :
    ∀ A : ℝ, 0 < A → ∀ ε : ℝ, 0 < ε → ∃ C X0 K δ : ℝ, δ < 1 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ ((55 / 100 + ε) * (595 / 1000 - 2 * ε)) ≤ H → H ≤ X →
        ∃ (Rv R0 M : ℕ → ℝ) (B1 B2 : ℕ → Prop),
          (cntIoc B1 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
          (cntIoc B2 X H : ℝ) ≤ C * H / Real.log X ^ A ∧
          (∀ n, InH2 n → ¬ B1 n → 0 < M n ∧ 16 / 100 * M n ≤ Rv n) ∧
          (∀ n, InH2 n → ¬ B2 n → R0 n ≤ K * M n * Real.log X ^ (δ - 1)) ∧
          (∀ n, InH2 n → 0 < Rv n - R0 n → IsPrimePlusPrimeSq n) := by
  sorry

/-! ### Bookkeeping helpers, full proofs -/

private theorem split_cnt_mono {S T : ℕ → Prop} (hST : ∀ n, S n → T n) (X H : ℝ) :
    cntIoc S X H ≤ cntIoc T X H := by
  unfold cntIoc
  have h : ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)) ⊆
      ((Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ T n)) := by
    intro n
    rw [Finset.mem_filter, Finset.mem_filter]
    rintro ⟨hn1, hXn, hSn⟩
    exact ⟨hn1, hXn, hST n hSn⟩
  exact Finset.card_le_card h

private theorem split_cnt_or_le (S T : ℕ → Prop) (X H : ℝ) :
    cntIoc (fun n => S n ∨ T n) X H ≤ cntIoc S X H + cntIoc T X H := by
  simp only [cntIoc, and_or_left, Finset.filter_or]
  exact Finset.card_union_le _ _

private theorem split_pos_of_main {M R R0 : ℝ} (hM : 0 < M) (hR : 16 / 100 * M ≤ R)
    (hR0 : R0 ≤ 1 / 20 * M) : 0 < R - R0 := by
  linarith

/-! ### Assembly -/

/-- ASSEMBLY, zero sorry of its own, from the four leaves above. The exception count at exponent
`0.3275` follows from the sieve input: an `n` in `H₂` which is not a prime plus a square of a prime
lies in the first or in the second bad set, because otherwise the main term exceeds the secondary
term and the difference would give a representation; the two bad sets are counted by `2 C H / L^A`.
The leaves make this conditional on the Section 5 output, exactly as the source's Theorem 2 is. -/
theorem kumchev_liu_thm2_03275_target_split : kumchev_liu_thm2_03275 := by
  intro A hA
  obtain ⟨C, X0, K, δ, hδ, h⟩ := sieve_inputs_03275 A hA (1 / 100) (by norm_num)
  obtain ⟨L0, hL0, hL⟩ := saving_beats_constant K δ hδ
  refine ⟨2 * C, max X0 (Real.exp L0), fun X H hX hH1 hH2 => ?_⟩
  have hX0 : X0 ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp L0 ≤ X := le_trans (le_max_right _ _) hX
  have h1X : 1 ≤ X := by
    have h1e : 1 < Real.exp L0 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hL0
    linarith
  have hlog : L0 ≤ Real.log X := by
    rw [← Real.log_exp L0]
    exact Real.log_le_log (Real.exp_pos L0) hXe
  have hexp : (55 / 100 + (1 : ℝ) / 100) * (595 / 1000 - 2 * ((1 : ℝ) / 100)) < 3275 / 10000 :=
    theta_exponent_03275 (by norm_num)
  have hrange : X ^ ((55 / 100 + (1 : ℝ) / 100) * (595 / 1000 - 2 * ((1 : ℝ) / 100))) ≤ H :=
    rpow_range_transfer h1X hexp.le hH1
  obtain ⟨Rv, R0, M, B1, B2, hB1, hB2, hmain, hprop2, hrep⟩ := h X H hX0 hrange hH2
  have hsub : ∀ n, (InH2 n ∧ ¬ IsPrimePlusPrimeSq n) → (B1 n ∨ B2 n) := by
    intro n ⟨hn, hnp⟩
    by_contra hc
    push Not at hc
    obtain ⟨hM, hRv⟩ := hmain n hn hc.1
    have hR0 := hprop2 n hn hc.2
    have hK : K * Real.log X ^ (δ - 1) ≤ 1 / 20 := hL _ hlog
    have hR0' : R0 n ≤ 1 / 20 * M n := by
      calc R0 n ≤ K * M n * Real.log X ^ (δ - 1) := hR0
        _ = (K * Real.log X ^ (δ - 1)) * M n := by ring
        _ ≤ 1 / 20 * M n := mul_le_mul_of_nonneg_right hK hM.le
    exact hnp (hrep n hn (split_pos_of_main hM hRv hR0'))
  have hc1 := split_cnt_mono hsub X H
  have hc2 := split_cnt_or_le B1 B2 X H
  have h3 : (cntIoc (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) X H : ℝ) ≤
      (cntIoc B1 X H : ℝ) + cntIoc B2 X H := by exact_mod_cast le_trans hc1 hc2
  calc (cntIoc (fun n => InH2 n ∧ ¬ IsPrimePlusPrimeSq n) X H : ℝ)
      ≤ C * H / Real.log X ^ A + C * H / Real.log X ^ A := by linarith
    _ = 2 * C * H / Real.log X ^ A := by ring

end LeanLab.KumchevLiu2007.Novelty1612

#print axioms LeanLab.KumchevLiu2007.Novelty1612.kumchev_liu_thm2_03275_target_split
