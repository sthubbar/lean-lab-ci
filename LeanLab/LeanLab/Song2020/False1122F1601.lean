/-
AI wrote the Lean code. CLAUDE S60 ROUTE BURST burst-20261122, 2026-11-22.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, Section 4, printed page 9.

FALSE: the leaf `DecompF1601.leaf_final_transfer_F1601` is refuted for every γ in range.
The leaf asks for the page 9 absorption to hold for EVERY D ≥ 0 that bounds |f - g|,
not for the D that Lemma 4 supplies. At y = n/3 the mean square of g is at least one,
since the prime 2 lies in the window, so a large enough admissible D breaks any C.
The paper's own step is unaffected; the assembly `logarithmic_transfer139_F1601`
therefore rests on a false leaf. `DecompF1601.lean` itself is not changed.
Binary Goldbach is open.
-/
import LeanLab.Song2020.DecompF1601

namespace LeanLab.Song2020.False1122F1601

open LeanLab.Song2020 LeanLab.Song2020.State1562
open scoped Classical

noncomputable section

/-- PROVED. `e(x)` has modulus one. -/
theorem norm_eC_one (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- PROVED. Page 9, the trivial estimate: |f - g| is at most the sum of the weights
plus the number of primes in the window. -/
theorem norm_fS_sub_gS_le (γ : ℝ) (n : ℕ) (y α : ℝ) :
    ‖fS γ n y α - gS n y α‖ ≤
      (∑ p ∈ (windowPrimes n y).filter (fun p => IsPSPrime γ p), |psWeight γ p|) +
        ((windowPrimes n y).card : ℝ) := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · unfold fS
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [norm_mul, norm_eC_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · unfold gS
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_eC_one]

/-- PROVED. For n > 3 the prime 2 lies in the window |p - n/3| < n/3. -/
theorem two_mem_window (n : ℕ) (hn : 3 < n) : 2 ∈ windowPrimes n ((n : ℝ) / 3) := by
  have hnR : (3 : ℝ) < n := by exact_mod_cast hn
  unfold windowPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, Nat.prime_two, ?_⟩
  · have h1 : (2 : ℝ) ≤ (n : ℝ) / 3 + (n : ℝ) / 3 := by linarith
    have h2 : (2 : ℝ) ≤ (⌈(n : ℝ) / 3 + (n : ℝ) / 3⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
    have h3 : 2 ≤ ⌈(n : ℝ) / 3 + (n : ℝ) / 3⌉₊ := by exact_mod_cast h2
    omega
  · rw [abs_lt]
    push_cast
    constructor <;> linarith

/-- PROVED, FALSE result. The negation of the statement of
`DecompF1601.leaf_final_transfer_F1601`, for every γ in range and every C₅. -/
theorem leaf_final_transfer_F1601_false (γ : ℝ) (hγ : 44 / 45 < γ) (hγ1 : γ < 1) :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∀ D : ℝ, 0 ≤ D → (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) →
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  rintro ⟨C, N₀, h⟩
  have hθ1 : songExponent γ < 1 := (songExponent_mem hγ hγ1).2
  have hpowlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - songExponent γ))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - songExponent γ)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpowlim.eventually_gt_atTop 3)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = max N₀ (max N2 4) := ⟨_, rfl⟩
  have hn4 : 4 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsmall : (n : ℝ) ^ songExponent γ < (n : ℝ) / 3 := by
    have hbig := hN2 n (by omega)
    have hpos := Real.rpow_pos_of_pos hn0 (songExponent γ)
    have he : (n : ℝ) ^ songExponent γ * (n : ℝ) ^ (1 - songExponent γ) = n := by
      rw [← Real.rpow_add hn0]
      ring_nf
      simp
    nlinarith [mul_lt_mul_of_pos_left hbig hpos]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B =
      (∑ p ∈ (windowPrimes n ((n : ℝ) / 3)).filter (fun p => IsPSPrime γ p),
        |psWeight γ p|) + ((windowPrimes n ((n : ℝ) / 3)).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact add_nonneg (Finset.sum_nonneg (fun p _ => abs_nonneg _)) (Nat.cast_nonneg _)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = C * (((n : ℝ) / 3) ^ 2 / Real.log (n : ℝ) ^ 4) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = B + |Q| + 1 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hDbound : ∀ α : ℝ, ‖fS γ n ((n : ℝ) / 3) α - gS n ((n : ℝ) / 3) α‖ ≤ D := by
    intro α
    refine (norm_fS_sub_gS_le γ n ((n : ℝ) / 3) α).trans ?_
    rw [← hB, hD]
    linarith [abs_nonneg Q]
  have key := h n (by omega) ((n : ℝ) / 3) hsmall le_rfl D hD0 hDbound
  rw [← hQ] at key
  have hf : 0 ≤ ∫ α in (0 : ℝ)..1, ‖fS γ n ((n : ℝ) / 3) α‖ ^ 2 := by
    rw [fS_mean_square139]
    exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hg : 1 ≤ ∫ α in (0 : ℝ)..1, ‖gS n ((n : ℝ) / 3) α‖ ^ 2 := by
    rw [gS_mean_square139]
    have hc : 0 < (windowPrimes n ((n : ℝ) / 3)).card :=
      Finset.card_pos.mpr ⟨2, two_mem_window n (by omega)⟩
    exact_mod_cast hc
  have hprod := mul_nonneg hD0
    (show 0 ≤ (∫ α in (0 : ℝ)..1, ‖fS γ n ((n : ℝ) / 3) α‖ ^ 2) +
      (∫ α in (0 : ℝ)..1, ‖gS n ((n : ℝ) / 3) α‖ ^ 2) - 1 by linarith)
  have hQle : Q ≤ |Q| := le_abs_self Q
  nlinarith

/-- PROVED, FALSE result. The negation of the full type of
`DecompF1601.leaf_final_transfer_F1601`, witnessed at γ = 89/90 and C₅ = 0. -/
theorem leaf_final_transfer_F1601_statement_false :
    ¬ ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ C₅ : ℝ, 0 ≤ C₅ →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∀ D : ℝ, 0 ≤ D → (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) →
          2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
              C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := fun h =>
  leaf_final_transfer_F1601_false (89 / 90) (by norm_num) (by norm_num)
    (h (89 / 90) (by norm_num) (by norm_num) 0 le_rfl)

/-- PROVED. The leaf's statement, exactly as sealed, is refuted: `DecompF1601.leaf_final_transfer_F1601`
has this type, so it cannot be proved. -/
theorem leaf_final_transfer_F1601_type_false :
    ¬ (type_of% @DecompF1601.leaf_final_transfer_F1601) :=
  leaf_final_transfer_F1601_statement_false

end

end LeanLab.Song2020.False1122F1601

#print axioms LeanLab.Song2020.False1122F1601.norm_eC_one
#print axioms LeanLab.Song2020.False1122F1601.norm_fS_sub_gS_le
#print axioms LeanLab.Song2020.False1122F1601.two_mem_window
#print axioms LeanLab.Song2020.False1122F1601.leaf_final_transfer_F1601_false
#print axioms LeanLab.Song2020.False1122F1601.leaf_final_transfer_F1601_statement_false
#print axioms LeanLab.Song2020.False1122F1601.leaf_final_transfer_F1601_type_false
